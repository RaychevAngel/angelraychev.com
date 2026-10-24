import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0311
import IrregularNine14P07C0312
import IrregularNine14P07C0313
import IrregularNine14P07C0314

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34200 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 168 19 496 464 464 464), lower := (rows 35 70 13 168 19 32 64 128 256), losses := [] }

theorem u34200 : Upper (D 7) (R 7) [34,68,9,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34201 : Route 9 := (fun mask => (mask,id))

def c34201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34201 : Upper (D 7) (R 7) [34,68,9,160,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,65] 13 (by decide) (choices 1) [2,16,128,256] r34201 c34201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18714
  · exact u18715
  · exact u18716
  · exact u18717

def b34202 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 168 82 433 465 401 401), lower := (rows 35 70 13 168 82 32 64 128 256), losses := [] }

theorem u34202 : Upper (D 7) (R 7) [34,68,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34203 : Route 9 := (fun mask => (mask,id))

def c34203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34203 : Upper (D 7) (R 7) [34,68,9,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,129] 13 (by decide) (choices 1) [2,16,64,256] r34203 c34203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18718
  · exact u18719
  · exact u18720
  · exact u18721

def r34204 : Route 9 := (fun mask => (mask,id))

def c34204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34204 : Upper (D 7) (R 7) [34,68,9,160,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,130] 13 (by decide) (choices 1) [1,16,64,256] r34204 c34204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18722
  · exact u18723
  · exact u18724
  · exact u18725

def r34205 : Route 9 := (fun mask => (mask,id))

def c34205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34205 : Upper (D 7) (R 7) [34,68,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,192] 13 (by decide) (choices 1) [1,2,16,256] r34205 c34205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18726
  · exact u18727
  · exact u18728
  · exact u18729

def r34206 : Route 9 := (fun mask => (mask,id))

def c34206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34206 : Upper (D 7) (R 7) [34,68,9,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,257] 13 (by decide) (choices 1) [2,16,64,128] r34206 c34206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18730
  · exact u18731
  · exact u18732
  · exact u18733

def r34207 : Route 9 := (fun mask => (mask,id))

def c34207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34207 : Upper (D 7) (R 7) [34,68,9,160,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,258] 13 (by decide) (choices 1) [1,16,64,128] r34207 c34207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18734
  · exact u18735
  · exact u18736
  · exact u18737

def r34208 : Route 9 := (fun mask => (mask,id))

def c34208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34208 : Upper (D 7) (R 7) [34,68,9,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,320] 13 (by decide) (choices 1) [1,2,16,128] r34208 c34208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18738
  · exact u18739
  · exact u18740
  · exact u18741

def r34209 : Route 9 := (fun mask => (mask,id))

def c34209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34209 : Upper (D 7) (R 7) [34,68,9,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,384] 13 (by decide) (choices 1) [1,2,16,64] r34209 c34209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18742
  · exact u18743
  · exact u18744
  · exact u18745

def b34210 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 200 19 432 496 432 432), lower := (rows 35 70 13 200 19 32 64 128 256), losses := [] }

theorem u34210 : Upper (D 7) (R 7) [34,68,9,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34211 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 200 49 434 466 402 402), lower := (rows 35 70 13 200 49 32 64 128 256), losses := [] }

theorem u34211 : Upper (D 7) (R 7) [34,68,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34212 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 13 200 50 433 465 401 401), lower := (rows 35 70 13 200 50 32 64 128 256), losses := [] }

theorem u34212 : Upper (D 7) (R 7) [34,68,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34213 : Route 9 := (fun mask => (mask,id))

def c34213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34213 : Upper (D 7) (R 7) [34,68,9,192,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,129] 13 (by decide) (choices 1) [2,16,256] r34213 c34213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18746
  · exact u18747
  · exact u18748

def r34214 : Route 9 := (fun mask => (mask,id))

def c34214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34214 : Upper (D 7) (R 7) [34,68,9,192,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,130] 13 (by decide) (choices 1) [1,16,256] r34214 c34214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18749
  · exact u18750
  · exact u18751

def r34215 : Route 9 := (fun mask => (mask,id))

def c34215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34215 : Upper (D 7) (R 7) [34,68,9,192,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,160] 13 (by decide) (choices 1) [1,2,16,256] r34215 c34215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18752
  · exact u18753
  · exact u18754
  · exact u18755

def r34216 : Route 9 := (fun mask => (mask,id))

def c34216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34216 : Upper (D 7) (R 7) [34,68,9,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,257] 13 (by decide) (choices 1) [2,16,128] r34216 c34216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18756
  · exact u18757
  · exact u18758

def r34217 : Route 9 := (fun mask => (mask,id))

def c34217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34217 : Upper (D 7) (R 7) [34,68,9,192,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,258] 13 (by decide) (choices 1) [1,16,128] r34217 c34217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18759
  · exact u18760
  · exact u18761

def r34218 : Route 9 := (fun mask => (mask,id))

def c34218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34218 : Upper (D 7) (R 7) [34,68,9,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,288] 13 (by decide) (choices 1) [1,2,16,128] r34218 c34218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18762
  · exact u18763
  · exact u18764
  · exact u18765

def r34219 : Route 9 := (fun mask => (mask,id))

def c34219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34219 : Upper (D 7) (R 7) [34,68,9,192,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,384] 13 (by decide) (choices 1) [1,2,16] r34219 c34219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18766
  · exact u18767
  · exact u18768

def b34220 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 70 13 266 49 240 208 208 464), lower := (rows 35 70 13 266 49 32 64 128 256), losses := [] }

theorem u34220 : Upper (D 7) (R 7) [34,68,9,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34221 : Route 9 := (fun mask => (mask,id))

def c34221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34221 : Upper (D 7) (R 7) [34,68,9,258,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,65] 13 (by decide) (choices 1) [16,128] r34221 c34221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18769
  · exact u18770

def r34222 : Route 9 := (fun mask => (mask,id))

def c34222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34222 : Upper (D 7) (R 7) [34,68,9,258,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,96] 13 (by decide) (choices 1) [1,16,128] r34222 c34222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18771
  · exact u18772
  · exact u18773

def r34223 : Route 9 := (fun mask => (mask,id))

def c34223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34223 : Upper (D 7) (R 7) [34,68,9,258,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,129] 13 (by decide) (choices 1) [16,64,128] r34223 c34223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18774
  · exact u18775
  · exact u18776

def r34224 : Route 9 := (fun mask => (mask,id))

def c34224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34224 : Upper (D 7) (R 7) [34,68,9,258,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,160] 13 (by decide) (choices 1) [1,16,64,128] r34224 c34224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18777
  · exact u18778
  · exact u18779
  · exact u18780

def r34225 : Route 9 := (fun mask => (mask,id))

def c34225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34225 : Upper (D 7) (R 7) [34,68,9,258,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,192] 13 (by decide) (choices 1) [1,16,128] r34225 c34225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18781
  · exact u18782
  · exact u18783

def b34226 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 280 19 224 224 224 480), lower := (rows 35 70 13 280 19 32 64 128 256), losses := [] }

theorem u34226 : Upper (D 7) (R 7) [34,68,9,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34227 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 13 280 49 226 194 194 450), lower := (rows 35 70 13 280 49 32 64 128 256), losses := [] }

theorem u34227 : Upper (D 7) (R 7) [34,68,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34228 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 13 280 50 225 193 193 449), lower := (rows 35 70 13 280 50 32 64 128 256), losses := [] }

theorem u34228 : Upper (D 7) (R 7) [34,68,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34229 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 161, targets := 64 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 35 70 13 280 81 162 226 162 418), lower := (rows 35 70 13 280 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 280 504 32 64 128 256) },{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 429 284 445 32 0 128 256) }] }

theorem u34229 : Upper (D 7) (R 7) [34,68,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34230 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 280 82 161 225 161 417), lower := (rows 35 70 13 280 82 32 64 128 256), losses := [] }

theorem u34230 : Upper (D 7) (R 7) [34,68,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34231 : Route 9 := (fun mask => (mask,id))

def c34231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34231 : Upper (D 7) (R 7) [34,68,9,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,96] 13 (by decide) (choices 1) [1,2,128] r34231 c34231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18784
  · exact u18785
  · exact u18786

def r34232 : Route 9 := (fun mask => (mask,id))

def c34232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34232 : Upper (D 7) (R 7) [34,68,9,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,129] 13 (by decide) (choices 1) [2,64,128] r34232 c34232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18787
  · exact u18788
  · exact u18789

def r34233 : Route 9 := (fun mask => (mask,id))

def c34233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34233 : Upper (D 7) (R 7) [34,68,9,272,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,130] 13 (by decide) (choices 1) [1,64,128] r34233 c34233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18790
  · exact u18791
  · exact u18792

def r34234 : Route 9 := (fun mask => (mask,id))

def c34234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34234 : Upper (D 7) (R 7) [34,68,9,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,160] 13 (by decide) (choices 1) [1,2,64,128] r34234 c34234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18793
  · exact u18794
  · exact u18795
  · exact u18796

def r34235 : Route 9 := (fun mask => (mask,id))

def c34235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34235 : Upper (D 7) (R 7) [34,68,9,272,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,192] 13 (by decide) (choices 1) [1,2,128] r34235 c34235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18797
  · exact u18798
  · exact u18799

def b34236 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 296 19 240 208 208 464), lower := (rows 35 70 13 296 19 32 64 128 256), losses := [] }

theorem u34236 : Upper (D 7) (R 7) [34,68,9,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34237 : Route 9 := (fun mask => (mask,id))

def c34237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34237 : Upper (D 7) (R 7) [34,68,9,288,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,65] 13 (by decide) (choices 1) [2,16,128] r34237 c34237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18800
  · exact u18801
  · exact u18802

def b34238 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 296 82 177 209 145 401), lower := (rows 35 70 13 296 82 32 64 128 256), losses := [] }

theorem u34238 : Upper (D 7) (R 7) [34,68,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34239 : Route 9 := (fun mask => (mask,id))

def c34239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34239 : Upper (D 7) (R 7) [34,68,9,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,129] 13 (by decide) (choices 1) [2,16,64,128] r34239 c34239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18803
  · exact u18804
  · exact u18805
  · exact u18806

def r34240 : Route 9 := (fun mask => (mask,id))

def c34240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34240 : Upper (D 7) (R 7) [34,68,9,288,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,130] 13 (by decide) (choices 1) [1,16,64,128] r34240 c34240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18807
  · exact u18808
  · exact u18809
  · exact u18810

def r34241 : Route 9 := (fun mask => (mask,id))

def c34241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34241 : Upper (D 7) (R 7) [34,68,9,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,192] 13 (by decide) (choices 1) [1,2,16,128] r34241 c34241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18811
  · exact u18812
  · exact u18813
  · exact u18814

def b34242 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 328 19 176 240 176 432), lower := (rows 35 70 13 328 19 32 64 128 256), losses := [] }

theorem u34242 : Upper (D 7) (R 7) [34,68,9,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34243 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 328 49 178 210 146 402), lower := (rows 35 70 13 328 49 32 64 128 256), losses := [] }

theorem u34243 : Upper (D 7) (R 7) [34,68,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34244 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 13 328 50 177 209 145 401), lower := (rows 35 70 13 328 50 32 64 128 256), losses := [] }

theorem u34244 : Upper (D 7) (R 7) [34,68,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34245 : Route 9 := (fun mask => (mask,id))

def c34245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34245 : Upper (D 7) (R 7) [34,68,9,320,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320,129] 13 (by decide) (choices 1) [2,16,128] r34245 c34245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18815
  · exact u18816
  · exact u18817

def r34246 : Route 9 := (fun mask => (mask,id))

def c34246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34246 : Upper (D 7) (R 7) [34,68,9,320,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320,130] 13 (by decide) (choices 1) [1,16,128] r34246 c34246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18818
  · exact u18819
  · exact u18820

def r34247 : Route 9 := (fun mask => (mask,id))

def c34247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34247 : Upper (D 7) (R 7) [34,68,9,320,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320,160] 13 (by decide) (choices 1) [1,2,16,128] r34247 c34247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18821
  · exact u18822
  · exact u18823
  · exact u18824

def b34248 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 70 13 392 19 240 240 240 496), lower := (rows 35 70 13 392 19 32 64 128 256), losses := [] }

theorem u34248 : Upper (D 7) (R 7) [34,68,9,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34249 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 70 13 392 49 242 210 210 466), lower := (rows 35 70 13 392 49 32 64 128 256), losses := [] }

theorem u34249 : Upper (D 7) (R 7) [34,68,9,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34250 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 70 13 392 50 241 209 209 465), lower := (rows 35 70 13 392 50 32 64 128 256), losses := [] }

theorem u34250 : Upper (D 7) (R 7) [34,68,9,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34251 : Route 9 := (fun mask => (mask,id))

def c34251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34251 : Upper (D 7) (R 7) [34,68,9,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,65] 13 (by decide) (choices 1) [2,16,128] r34251 c34251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18825
  · exact u18826
  · exact u18827

def b34252 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 392 82 177 241 177 433), lower := (rows 35 70 13 392 82 32 64 128 256), losses := [] }

theorem u34252 : Upper (D 7) (R 7) [34,68,9,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34253 : Route 9 := (fun mask => (mask,id))

def c34253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34253 : Upper (D 7) (R 7) [34,68,9,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96] 13 (by decide) (choices 1) [1,2,16,128] r34253 c34253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18828
  · exact u18829
  · exact u18830
  · exact u18831

def r34254 : Route 9 := (fun mask => (mask,id))

def c34254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34254 : Upper (D 7) (R 7) [34,68,9,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,129] 13 (by decide) (choices 1) [2,16,64] r34254 c34254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18832
  · exact u18833
  · exact u18834

def r34255 : Route 9 := (fun mask => (mask,id))

def c34255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34255 : Upper (D 7) (R 7) [34,68,9,384,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,130] 13 (by decide) (choices 1) [1,16,64] r34255 c34255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18835
  · exact u18836
  · exact u18837

def r34256 : Route 9 := (fun mask => (mask,id))

def c34256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34256 : Upper (D 7) (R 7) [34,68,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,160] 13 (by decide) (choices 1) [1,2,16,64] r34256 c34256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18838
  · exact u18839
  · exact u18840
  · exact u18841

def r34257 : Route 9 := (fun mask => (mask,id))

def c34257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34257 : Upper (D 7) (R 7) [34,68,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192] 13 (by decide) (choices 1) [1,2,16] r34257 c34257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18842
  · exact u18843
  · exact u18844

def b34258 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 14 25 49 480 448 448 448), lower := (rows 35 70 14 25 49 32 64 128 256), losses := [] }

theorem u34258 : Upper (D 7) (R 7) [34,68,10,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34259 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 14, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 14 25 81 416 480 416 416), lower := (rows 35 70 14 25 81 32 64 128 256), losses := [] }

theorem u34259 : Upper (D 7) (R 7) [34,68,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34259
end Delivery.IrregularNine14.P07
