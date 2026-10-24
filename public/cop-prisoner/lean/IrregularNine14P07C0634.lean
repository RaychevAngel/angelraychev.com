import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0417
import IrregularNine14P07C0418
import IrregularNine14P07C0419

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38040 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 28 11 208 291 355 419 291), lower := (rows 37 194 28 11 208 32 64 128 256), losses := [] }

theorem u38040 : Upper (D 7) (R 7) [36,192,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38041 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38041 : Upper (D 7) (R 7) [36,192,24,3,257] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,257] 13 (by decide) (choices 1) [2,64] r38041 c38041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25073
  · exact u25074

def r38042 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38042 : Upper (D 7) (R 7) [36,192,24,3,258] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,258] 13 (by decide) (choices 1) [1,64] r38042 c38042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25075
  · exact u25076

def r38043 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38043 : Upper (D 7) (R 7) [36,192,24,3,288] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,288] 13 (by decide) (choices 1) [1,2,64] r38043 c38043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25077
  · exact u25078
  · exact u25079

def r38044 : Route 9 := (fun mask => (mask,id))

def c38044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38044 : Upper (D 7) (R 7) [36,192,24,3,320] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,320] 13 (by decide) (choices 1) [1,2,128] r38044 c38044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25080
  · exact u25081
  · exact u25082

def b38045 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 28 41 81 418 450 386 386), lower := (rows 37 194 28 41 81 32 64 128 256), losses := [] }

theorem u38045 : Upper (D 7) (R 7) [36,192,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38046 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 28 41 273 226 194 194 450), lower := (rows 37 194 28 41 273 32 64 128 256), losses := [] }

theorem u38046 : Upper (D 7) (R 7) [36,192,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38047 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 28 41 274 227 195 195 451), lower := (rows 37 194 28 41 274 32 64 128 256), losses := [] }

theorem u38047 : Upper (D 7) (R 7) [36,192,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38048 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 28 41 336 163 195 131 387), lower := (rows 37 194 28 41 336 32 64 128 256), losses := [] }

theorem u38048 : Upper (D 7) (R 7) [36,192,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38049 : Route 9 := (fun mask => (mask,id))

def c38049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38049 : Upper (D 7) (R 7) [36,192,24,34,65] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34,65] 13 (by decide) (choices 1) [1,2,128,256] r38049 c38049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25083
  · exact u25084
  · exact u25085
  · exact u25086

def b38050 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 28 42 82 417 449 385 385), lower := (rows 37 194 28 42 82 32 64 128 256), losses := [] }

theorem u38050 : Upper (D 7) (R 7) [36,192,24,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38051 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 37 194 28 42 208 291 323 387 259), lower := (rows 37 194 28 42 208 32 64 128 256), losses := [] }

theorem u38051 : Upper (D 7) (R 7) [36,192,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38052 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38052 : Upper (D 7) (R 7) [36,192,24,34,257] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34,257] 13 (by decide) (choices 1) [1,2,64] r38052 c38052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25087
  · exact u25088
  · exact u25089

def r38053 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38053 : Upper (D 7) (R 7) [36,192,24,34,258] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34,258] 13 (by decide) (choices 1) [1,64] r38053 c38053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25090
  · exact u25091

def r38054 : Route 9 := (fun mask => (mask,id))

def c38054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38054 : Upper (D 7) (R 7) [36,192,24,34,320] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34,320] 13 (by decide) (choices 1) [1,2,128] r38054 c38054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25092
  · exact u25093
  · exact u25094

def r38055 : Route 9 := (fun mask => (mask,id))

def c38055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38055 : Upper (D 7) (R 7) [36,192,24,65,129] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,129] 13 (by decide) (choices 1) [2,256] r38055 c38055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25095
  · exact u25096

def b38056 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 28 73 146 291 355 419 291), lower := (rows 37 194 28 73 146 32 64 128 256), losses := [] }

theorem u38056 : Upper (D 7) (R 7) [36,192,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38057 : Route 9 := (fun mask => (mask,id))

def c38057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38057 : Upper (D 7) (R 7) [36,192,24,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,160] 13 (by decide) (choices 1) [1,2,256] r38057 c38057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25097
  · exact u25098
  · exact u25099

def r38058 : Route 9 := (fun mask => (mask,id))

def c38058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38058 : Upper (D 7) (R 7) [36,192,24,65,257] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,257] 13 (by decide) (choices 1) [2,128] r38058 c38058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25100
  · exact u25101

def r38059 : Route 9 := (fun mask => (mask,id))

def c38059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38059 : Upper (D 7) (R 7) [36,192,24,65,258] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,258] 13 (by decide) (choices 1) [1,2,128] r38059 c38059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25102
  · exact u25103
  · exact u25104

def r38060 : Route 9 := (fun mask => (mask,id))

def c38060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38060 : Upper (D 7) (R 7) [36,192,24,65,288] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,288] 13 (by decide) (choices 1) [1,2,128] r38060 c38060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25105
  · exact u25106
  · exact u25107

def r38061 : Route 9 := (fun mask => (mask,id))

def c38061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38061 : Upper (D 7) (R 7) [36,192,24,65,384] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,384] 13 (by decide) (choices 1) [1,2] r38061 c38061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25108
  · exact u25109

def b38062 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 176 291 323 387 259), lower := (rows 37 194 28 74 176 32 64 128 256), losses := [] }

theorem u38062 : Upper (D 7) (R 7) [36,192,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38063 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 273 163 227 163 419), lower := (rows 37 194 28 74 273 32 64 128 256), losses := [] }

theorem u38063 : Upper (D 7) (R 7) [36,192,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38064 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 274 161 225 161 417), lower := (rows 37 194 28 74 274 32 64 128 256), losses := [] }

theorem u38064 : Upper (D 7) (R 7) [36,192,24,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38065 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 304 163 195 131 387), lower := (rows 37 194 28 74 304 32 64 128 256), losses := [] }

theorem u38065 : Upper (D 7) (R 7) [36,192,24,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38066 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 400 35 99 163 291), lower := (rows 37 194 28 74 400 32 64 128 256), losses := [] }

theorem u38066 : Upper (D 7) (R 7) [36,192,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38067 : Route 9 := (fun mask => (mask,id))

def c38067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38067 : Upper (D 7) (R 7) [36,192,24,96,257] 13 := by
  apply FastRouting.sound _ _ [36,192,24,96,257] 13 (by decide) (choices 1) [1,2,128] r38067 c38067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25110
  · exact u25111
  · exact u25112

def r38068 : Route 9 := (fun mask => (mask,id))

def c38068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38068 : Upper (D 7) (R 7) [36,192,24,96,258] 13 := by
  apply FastRouting.sound _ _ [36,192,24,96,258] 13 (by decide) (choices 1) [1,2,128] r38068 c38068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25113
  · exact u25114
  · exact u25115

def r38069 : Route 9 := (fun mask => (mask,id))

def c38069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38069 : Upper (D 7) (R 7) [36,192,24,96,384] 13 := by
  apply FastRouting.sound _ _ [36,192,24,96,384] 13 (by decide) (choices 1) [1,2] r38069 c38069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25116
  · exact u25117

def b38070 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 28 200 273 35 99 163 291), lower := (rows 37 194 28 200 273 32 64 128 256), losses := [] }

theorem u38070 : Upper (D 7) (R 7) [36,192,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38071 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 28 200 274 35 99 163 291), lower := (rows 37 194 28 200 274 32 64 128 256), losses := [] }

theorem u38071 : Upper (D 7) (R 7) [36,192,24,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38072 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 1, region := 8, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(1,5),(3,0),(3,1),(3,5)], upper := (rows 37 194 28 200 304 35 67 131 259), lower := (rows 37 194 28 200 304 32 64 128 256), losses := [] }

theorem u38072 : Upper (D 7) (R 7) [36,192,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38073 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 16, targets := 160 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 37 194 69 11 26 432 496 432 432), lower := (rows 37 194 69 11 26 32 64 128 256), losses := [] }

theorem u38073 : Upper (D 7) (R 7) [36,192,65,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38074 : Route 9 := (fun mask => (mask,id))

def c38074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u38074 : Upper (D 7) (R 7) [36,192,65,3,34] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,34] 13 (by decide) (choices 1) [8,16,128,256] r38074 c38074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25118
  · exact u25119
  · exact u25120
  · exact u25121

def b38075 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,6)], upper := (rows 37 194 69 11 56 434 466 402 402), lower := (rows 37 194 69 11 56 32 64 128 256), losses := [] }

theorem u38075 : Upper (D 7) (R 7) [36,192,65,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38076 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 69 11 146 312 376 440 312), lower := (rows 37 194 69 11 146 32 64 128 256), losses := [] }

theorem u38076 : Upper (D 7) (R 7) [36,192,65,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38077 : Route 9 := (fun mask => (mask,id))

def c38077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38077 : Upper (D 7) (R 7) [36,192,65,3,136] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,136] 13 (by decide) (choices 1) [2,16,256] r38077 c38077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25122
  · exact u25123
  · exact u25124

def r38078 : Route 9 := (fun mask => (mask,id))

def c38078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38078 : Upper (D 7) (R 7) [36,192,65,3,160] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,160] 13 (by decide) (choices 1) [2,8,16,256] r38078 c38078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25125
  · exact u25126
  · exact u25127
  · exact u25128

def r38079 : Route 9 := (fun mask => (mask,id))

def c38079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38079 : Upper (D 7) (R 7) [36,192,65,3,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,258] 13 (by decide) (choices 1) [8,16,128] r38079 c38079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25129
  · exact u25130
  · exact u25131

def r38080 : Route 9 := (fun mask => (mask,id))

def c38080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38080 : Upper (D 7) (R 7) [36,192,65,3,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,264] 13 (by decide) (choices 1) [2,16,128] r38080 c38080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25132
  · exact u25133
  · exact u25134

def r38081 : Route 9 := (fun mask => (mask,id))

def c38081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38081 : Upper (D 7) (R 7) [36,192,65,3,288] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,288] 13 (by decide) (choices 1) [2,8,16,128] r38081 c38081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25135
  · exact u25136
  · exact u25137
  · exact u25138

def r38082 : Route 9 := (fun mask => (mask,id))

def c38082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38082 : Upper (D 7) (R 7) [36,192,65,3,384] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3,384] 13 (by decide) (choices 1) [2,8,16] r38082 c38082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25139
  · exact u25140
  · exact u25141

def r38083 : Route 9 := (fun mask => (mask,id))

def c38083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38083 : Upper (D 7) (R 7) [36,192,65,17,10] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,10] 13 (by decide) (choices 1) [2,128,256] r38083 c38083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25142
  · exact u25143
  · exact u25144

def b38084 : PairBound 9 := { available := 394, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 69 25 50 426 458 394 394), lower := (rows 37 194 69 25 50 32 64 128 256), losses := [] }

theorem u38084 : Upper (D 7) (R 7) [36,192,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38085 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 69 25 56 418 450 386 386), lower := (rows 37 194 69 25 56 32 64 128 256), losses := [] }

theorem u38085 : Upper (D 7) (R 7) [36,192,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38086 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 69 25 146 298 362 426 298), lower := (rows 37 194 69 25 146 32 64 128 256), losses := [] }

theorem u38086 : Upper (D 7) (R 7) [36,192,65,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38087 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 25 152 290 354 418 290), lower := (rows 37 194 69 25 152 32 64 128 256), losses := [] }

theorem u38087 : Upper (D 7) (R 7) [36,192,65,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38088 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 69 25 176 298 330 394 266), lower := (rows 37 194 69 25 176 32 64 128 256), losses := [] }

theorem u38088 : Upper (D 7) (R 7) [36,192,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38089 : Route 9 := (fun mask => (mask,id))

def c38089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38089 : Upper (D 7) (R 7) [36,192,65,17,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,258] 13 (by decide) (choices 1) [2,8,128] r38089 c38089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25145
  · exact u25146
  · exact u25147

def r38090 : Route 9 := (fun mask => (mask,id))

def c38090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38090 : Upper (D 7) (R 7) [36,192,65,17,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,264] 13 (by decide) (choices 1) [2,128] r38090 c38090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25148
  · exact u25149

def b38091 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 69 25 304 170 202 138 394), lower := (rows 37 194 69 25 304 32 64 128 256), losses := [] }

theorem u38091 : Upper (D 7) (R 7) [36,192,65,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38092 : Route 9 := (fun mask => (mask,id))

def c38092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38092 : Upper (D 7) (R 7) [36,192,65,17,384] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17,384] 13 (by decide) (choices 1) [2,8] r38092 c38092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25150
  · exact u25151

def b38093 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 69 26 26 417 481 417 417), lower := (rows 37 194 69 26 26 32 64 128 256), losses := [] }

theorem u38093 : Upper (D 7) (R 7) [36,192,65,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38094 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 69 26 49 426 458 394 394), lower := (rows 37 194 69 26 49 32 64 128 256), losses := [] }

theorem u38094 : Upper (D 7) (R 7) [36,192,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38095 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 69 26 50 425 457 393 393), lower := (rows 37 194 69 26 50 32 64 128 256), losses := [] }

theorem u38095 : Upper (D 7) (R 7) [36,192,65,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38096 : Route 9 := (fun mask => (mask,id))

def c38096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38096 : Upper (D 7) (R 7) [36,192,65,18,40] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,40] 13 (by decide) (choices 1) [1,2,128,256] r38096 c38096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25152
  · exact u25153
  · exact u25154
  · exact u25155

def b38097 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 69 26 145 298 362 426 298), lower := (rows 37 194 69 26 145 32 64 128 256), losses := [] }

theorem u38097 : Upper (D 7) (R 7) [36,192,65,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38098 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 194 69 26 146 297 361 425 297), lower := (rows 37 194 69 26 146 32 64 128 256), losses := [] }

theorem u38098 : Upper (D 7) (R 7) [36,192,65,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38099 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 194 69 26 152 291 355 419 291), lower := (rows 37 194 69 26 152 32 64 128 256), losses := [] }

theorem u38099 : Upper (D 7) (R 7) [36,192,65,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38099
end Delivery.IrregularNine14.P07
