import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0295
import IrregularNine14P06C0296

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34200 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 162 261 28 49 102 70 198 326), lower := (rows 11 162 261 28 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 130 453 28 477 0 64 128 256) }] }

theorem u34200 : Upper (D 6) (R 6) [10,160,257,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34201 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 261 28 50 101 69 197 325), lower := (rows 11 162 261 28 50 32 64 128 256), losses := [] }

theorem u34201 : Upper (D 6) (R 6) [10,160,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34202 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 261 28 52 99 67 195 323), lower := (rows 11 162 261 28 52 32 64 128 256), losses := [] }

theorem u34202 : Upper (D 6) (R 6) [10,160,257,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34203 : Route 9 := (fun mask => (mask,id))

def c34203 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34203 : Upper (D 6) (R 6) [10,160,257,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,65] 13 (by decide) (choices 1) [2,4,64] r34203 c34203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17705
  · exact u17706
  · exact u17707

def r34204 : Route 9 := (fun mask => (mask,id))

def c34204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34204 : Upper (D 6) (R 6) [10,160,257,20,66] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,66] 13 (by decide) (choices 1) [1,4,64] r34204 c34204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17708
  · exact u17709
  · exact u17710

def b34205 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 261 28 84 99 99 227 355), lower := (rows 11 162 261 28 84 32 64 128 256), losses := [] }

theorem u34205 : Upper (D 6) (R 6) [10,160,257,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34206 : Route 9 := (fun mask => (mask,id))

def c34206 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34206 : Upper (D 6) (R 6) [10,160,257,20,96] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,96] 13 (by decide) (choices 1) [1,2,4,64] r34206 c34206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17711
  · exact u17712
  · exact u17713
  · exact u17714

def b34207 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 261 44 19 116 84 212 340), lower := (rows 11 162 261 44 19 32 64 128 256), losses := [] }

theorem u34207 : Upper (D 6) (R 6) [10,160,257,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34208 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 261 44 21 114 82 210 338), lower := (rows 11 162 261 44 21 32 64 128 256), losses := [] }

theorem u34208 : Upper (D 6) (R 6) [10,160,257,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34209 : Route 9 := (fun mask => (mask,id))

def c34209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34209 : Upper (D 6) (R 6) [10,160,257,36,6] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,6] 13 (by decide) (choices 1) [1,16,64] r34209 c34209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17715
  · exact u17716
  · exact u17717

def r34210 : Route 9 := (fun mask => (mask,id))

def c34210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34210 : Upper (D 6) (R 6) [10,160,257,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,65] 13 (by decide) (choices 1) [2,4,16,64] r34210 c34210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17718
  · exact u17719
  · exact u17720
  · exact u17721

def r34211 : Route 9 := (fun mask => (mask,id))

def c34211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34211 : Upper (D 6) (R 6) [10,160,257,36,66] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,66] 13 (by decide) (choices 1) [1,4,16,64] r34211 c34211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17722
  · exact u17723
  · exact u17724
  · exact u17725

def r34212 : Route 9 := (fun mask => (mask,id))

def c34212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34212 : Upper (D 6) (R 6) [10,160,257,36,68] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,68] 13 (by decide) (choices 1) [1,2,16,64] r34212 c34212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17726
  · exact u17727
  · exact u17728
  · exact u17729

def b34213 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 261 56 19 100 68 196 324), lower := (rows 11 162 261 56 19 32 64 128 256), losses := [] }

theorem u34213 : Upper (D 6) (R 6) [10,160,257,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34214 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 261 56 21 102 70 198 326), lower := (rows 11 162 261 56 21 32 64 128 256), losses := [] }

theorem u34214 : Upper (D 6) (R 6) [10,160,257,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34215 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 261 56 22 101 69 197 325), lower := (rows 11 162 261 56 22 32 64 128 256), losses := [] }

theorem u34215 : Upper (D 6) (R 6) [10,160,257,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34216 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 261 56 81 102 70 198 326), lower := (rows 11 162 261 56 81 32 64 128 256), losses := [] }

theorem u34216 : Upper (D 6) (R 6) [10,160,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34217 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 261 56 82 101 69 197 325), lower := (rows 11 162 261 56 82 32 64 128 256), losses := [] }

theorem u34217 : Upper (D 6) (R 6) [10,160,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34218 : Route 9 := (fun mask => (mask,id))

def c34218 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34218 : Upper (D 6) (R 6) [10,160,257,48,68] 13 := by
  apply FastRouting.sound _ _ [10,160,257,48,68] 13 (by decide) (choices 1) [1,2,4,64] r34218 c34218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17730
  · exact u17731
  · exact u17732
  · exact u17733

def r34219 : Route 9 := (fun mask => (mask,id))

def c34219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34219 : Upper (D 6) (R 6) [10,160,257,65,6] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,6] 13 (by decide) (choices 1) [4,16,64] r34219 c34219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17734
  · exact u17735
  · exact u17736

def b34220 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 261 73 50 116 84 212 340), lower := (rows 11 162 261 73 50 32 64 128 256), losses := [] }

theorem u34220 : Upper (D 6) (R 6) [10,160,257,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34221 : Route 9 := (fun mask => (mask,id))

def c34221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34221 : Upper (D 6) (R 6) [10,160,257,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,36] 13 (by decide) (choices 1) [2,4,16,64] r34221 c34221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17737
  · exact u17738
  · exact u17739
  · exact u17740

def b34222 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 261 73 82 52 116 180 308), lower := (rows 11 162 261 73 82 32 64 128 256), losses := [] }

theorem u34222 : Upper (D 6) (R 6) [10,160,257,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34223 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 261 73 84 54 118 182 310), lower := (rows 11 162 261 73 84 32 64 128 256), losses := [] }

theorem u34223 : Upper (D 6) (R 6) [10,160,257,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34224 : Route 9 := (fun mask => (mask,id))

def c34224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34224 : Upper (D 6) (R 6) [10,160,257,65,96] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,96] 13 (by decide) (choices 1) [2,4,16] r34224 c34224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17741
  · exact u17742
  · exact u17743

def b34225 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 261 76 19 116 116 244 372), lower := (rows 11 162 261 76 19 32 64 128 256), losses := [] }

theorem u34225 : Upper (D 6) (R 6) [10,160,257,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34226 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 261 76 21 114 114 242 370), lower := (rows 11 162 261 76 21 32 64 128 256), losses := [] }

theorem u34226 : Upper (D 6) (R 6) [10,160,257,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34227 : Route 9 := (fun mask => (mask,id))

def c34227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34227 : Upper (D 6) (R 6) [10,160,257,68,6] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,6] 13 (by decide) (choices 1) [1,16,64] r34227 c34227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17744
  · exact u17745
  · exact u17746

def r34228 : Route 9 := (fun mask => (mask,id))

def c34228 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34228 : Upper (D 6) (R 6) [10,160,257,68,33] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,33] 13 (by decide) (choices 1) [2,4,16,64] r34228 c34228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17747
  · exact u17748
  · exact u17749
  · exact u17750

def b34229 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 261 76 50 117 85 213 341), lower := (rows 11 162 261 76 50 32 64 128 256), losses := [] }

theorem u34229 : Upper (D 6) (R 6) [10,160,257,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34230 : Route 9 := (fun mask => (mask,id))

def c34230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34230 : Upper (D 6) (R 6) [10,160,257,68,36] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,36] 13 (by decide) (choices 1) [1,2,16,64] r34230 c34230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17751
  · exact u17752
  · exact u17753
  · exact u17754

def r34231 : Route 9 := (fun mask => (mask,id))

def c34231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34231 : Upper (D 6) (R 6) [10,160,257,68,65] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,65] 13 (by decide) (choices 1) [2,4,16] r34231 c34231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17755
  · exact u17756
  · exact u17757

def r34232 : Route 9 := (fun mask => (mask,id))

def c34232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34232 : Upper (D 6) (R 6) [10,160,257,68,66] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,66] 13 (by decide) (choices 1) [1,4,16] r34232 c34232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17758
  · exact u17759
  · exact u17760

def b34233 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 261 76 84 51 115 179 307), lower := (rows 11 162 261 76 84 32 64 128 256), losses := [] }

theorem u34233 : Upper (D 6) (R 6) [10,160,257,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34234 : Route 9 := (fun mask => (mask,id))

def c34234 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34234 : Upper (D 6) (R 6) [10,160,257,68,96] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,96] 13 (by decide) (choices 1) [1,2,4,16] r34234 c34234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17761
  · exact u17762
  · exact u17763
  · exact u17764

def b34235 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 261 88 19 100 100 228 356), lower := (rows 11 162 261 88 19 32 64 128 256), losses := [] }

theorem u34235 : Upper (D 6) (R 6) [10,160,257,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34236 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 261 88 21 102 102 230 358), lower := (rows 11 162 261 88 21 32 64 128 256), losses := [] }

theorem u34236 : Upper (D 6) (R 6) [10,160,257,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34237 : Route 9 := (fun mask => (mask,id))

def c34237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34237 : Upper (D 6) (R 6) [10,160,257,80,6] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,6] 13 (by decide) (choices 1) [1,4,64] r34237 c34237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17765
  · exact u17766
  · exact u17767

def b34238 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 162 261 88 49 102 70 198 326), lower := (rows 11 162 261 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 130 453 92 477 0 64 128 256) }] }

theorem u34238 : Upper (D 6) (R 6) [10,160,257,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34239 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 261 88 50 101 69 197 325), lower := (rows 11 162 261 88 50 32 64 128 256), losses := [] }

theorem u34239 : Upper (D 6) (R 6) [10,160,257,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34240 : Route 9 := (fun mask => (mask,id))

def c34240 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34240 : Upper (D 6) (R 6) [10,160,257,80,36] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,36] 13 (by decide) (choices 1) [1,2,4,64] r34240 c34240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17768
  · exact u17769
  · exact u17770
  · exact u17771

def b34241 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 261 88 81 38 102 166 294), lower := (rows 11 162 261 88 81 32 64 128 256), losses := [] }

theorem u34241 : Upper (D 6) (R 6) [10,160,257,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34242 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 261 88 82 37 101 165 293), lower := (rows 11 162 261 88 82 32 64 128 256), losses := [] }

theorem u34242 : Upper (D 6) (R 6) [10,160,257,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34243 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 261 88 84 39 103 167 295), lower := (rows 11 162 261 88 84 32 64 128 256), losses := [] }

theorem u34243 : Upper (D 6) (R 6) [10,160,257,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34244 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 261 88 112 39 71 135 263), lower := (rows 11 162 261 88 112 32 64 128 256), losses := [] }

theorem u34244 : Upper (D 6) (R 6) [10,160,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34245 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 261 104 19 116 84 212 340), lower := (rows 11 162 261 104 19 32 64 128 256), losses := [] }

theorem u34245 : Upper (D 6) (R 6) [10,160,257,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34246 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 261 104 21 118 86 214 342), lower := (rows 11 162 261 104 21 32 64 128 256), losses := [] }

theorem u34246 : Upper (D 6) (R 6) [10,160,257,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34247 : Route 9 := (fun mask => (mask,id))

def c34247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34247 : Upper (D 6) (R 6) [10,160,257,96,6] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96,6] 13 (by decide) (choices 1) [1,4,16,64] r34247 c34247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17772
  · exact u17773
  · exact u17774
  · exact u17775

def b34248 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 261 104 81 54 86 150 278), lower := (rows 11 162 261 104 81 32 64 128 256), losses := [] }

theorem u34248 : Upper (D 6) (R 6) [10,160,257,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34249 : Route 9 := (fun mask => (mask,id))

def c34249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34249 : Upper (D 6) (R 6) [10,160,257,96,66] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96,66] 13 (by decide) (choices 1) [1,4,16] r34249 c34249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17776
  · exact u17777
  · exact u17778

def r34250 : Route 9 := (fun mask => (mask,id))

def c34250 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34250 : Upper (D 6) (R 6) [10,160,257,96,68] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96,68] 13 (by decide) (choices 1) [1,2,4,16] r34250 c34250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17779
  · exact u17780
  · exact u17781
  · exact u17782

def b34251 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 262 25 21 100 100 228 356), lower := (rows 11 162 262 25 21 32 64 128 256), losses := [] }

theorem u34251 : Upper (D 6) (R 6) [10,160,258,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34252 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 262 25 49 100 68 196 324), lower := (rows 11 162 262 25 49 32 64 128 256), losses := [] }

theorem u34252 : Upper (D 6) (R 6) [10,160,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34253 : Route 9 := (fun mask => (mask,id))

def c34253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34253 : Upper (D 6) (R 6) [10,160,258,17,36] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,36] 13 (by decide) (choices 1) [1,4,64] r34253 c34253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17783
  · exact u17784
  · exact u17785

def b34254 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 262 25 81 100 100 228 356), lower := (rows 11 162 262 25 81 32 64 128 256), losses := [] }

theorem u34254 : Upper (D 6) (R 6) [10,160,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34255 : Route 9 := (fun mask => (mask,id))

def c34255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34255 : Upper (D 6) (R 6) [10,160,258,17,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,68] 13 (by decide) (choices 1) [1,4,64] r34255 c34255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17786
  · exact u17787
  · exact u17788

def r34256 : Route 9 := (fun mask => (mask,id))

def c34256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34256 : Upper (D 6) (R 6) [10,160,258,17,96] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,96] 13 (by decide) (choices 1) [1,4,64] r34256 c34256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17789
  · exact u17790
  · exact u17791

def b34257 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 262 28 21 97 97 225 353), lower := (rows 11 162 262 28 21 32 64 128 256), losses := [] }

theorem u34257 : Upper (D 6) (R 6) [10,160,258,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34258 : Route 9 := (fun mask => (mask,id))

def c34258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34258 : Upper (D 6) (R 6) [10,160,258,20,33] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,33] 13 (by decide) (choices 1) [1,4,64] r34258 c34258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17792
  · exact u17793
  · exact u17794

def b34259 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 262 28 52 97 65 193 321), lower := (rows 11 162 262 28 52 32 64 128 256), losses := [] }

theorem u34259 : Upper (D 6) (R 6) [10,160,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34259
end Delivery.IrregularNine14.P06
