import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0270
import IrregularNine14P07C0271

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32760 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 137 304 226 194 194 450), lower := (rows 13 50 69 137 304 32 64 128 256), losses := [] }

theorem u32760 : Upper (D 7) (R 7) [12,48,65,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32761 : Route 9 := (fun mask => (mask,id))

def c32761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32761 : Upper (D 7) (R 7) [12,48,65,129,320] 13 := by
  apply FastRouting.sound _ _ [12,48,65,129,320] 13 (by decide) (choices 1) [2,128] r32761 c32761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16204
  · exact u16205

def b32762 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 13 50 69 138 19 480 480 480 480), lower := (rows 13 50 69 138 19 32 64 128 256), losses := [] }

theorem u32762 : Upper (D 7) (R 7) [12,48,65,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32763 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 138 49 482 450 450 450), lower := (rows 13 50 69 138 49 32 64 128 256), losses := [] }

theorem u32763 : Upper (D 7) (R 7) [12,48,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32764 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 138 50 481 449 449 449), lower := (rows 13 50 69 138 50 32 64 128 256), losses := [] }

theorem u32764 : Upper (D 7) (R 7) [12,48,65,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32765 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 50 69 138 81 418 482 418 418), lower := (rows 13 50 69 138 81 32 64 128 256), losses := [] }

theorem u32765 : Upper (D 7) (R 7) [12,48,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32766 : Route 9 := (fun mask => (mask,id))

def c32766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32766 : Upper (D 7) (R 7) [12,48,65,130,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,66] 13 (by decide) (choices 1) [1,128,256] r32766 c32766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16206
  · exact u16207
  · exact u16208

def b32767 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 138 112 419 451 387 387), lower := (rows 13 50 69 138 112 32 64 128 256), losses := [] }

theorem u32767 : Upper (D 7) (R 7) [12,48,65,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32768 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 13 50 69 138 145 354 354 482 354), lower := (rows 13 50 69 138 145 32 64 128 256), losses := [] }

theorem u32768 : Upper (D 7) (R 7) [12,48,65,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32769 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 13 50 69 138 146 353 353 481 353), lower := (rows 13 50 69 138 146 32 64 128 256), losses := [] }

theorem u32769 : Upper (D 7) (R 7) [12,48,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32770 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 138 176 355 323 451 323), lower := (rows 13 50 69 138 176 32 64 128 256), losses := [] }

theorem u32770 : Upper (D 7) (R 7) [12,48,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32771 : Route 9 := (fun mask => (mask,id))

def c32771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32771 : Upper (D 7) (R 7) [12,48,65,130,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,192] 13 (by decide) (choices 1) [1,2,256] r32771 c32771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16209
  · exact u16210
  · exact u16211

def r32772 : Route 9 := (fun mask => (mask,id))

def c32772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32772 : Upper (D 7) (R 7) [12,48,65,130,257] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,257] 13 (by decide) (choices 1) [2,64,128] r32772 c32772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16212
  · exact u16213
  · exact u16214

def r32773 : Route 9 := (fun mask => (mask,id))

def c32773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32773 : Upper (D 7) (R 7) [12,48,65,130,258] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,258] 13 (by decide) (choices 1) [1,64,128] r32773 c32773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16215
  · exact u16216
  · exact u16217

def b32774 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 138 304 227 195 195 451), lower := (rows 13 50 69 138 304 32 64 128 256), losses := [] }

theorem u32774 : Upper (D 7) (R 7) [12,48,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32775 : Route 9 := (fun mask => (mask,id))

def c32775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32775 : Upper (D 7) (R 7) [12,48,65,130,320] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,320] 13 (by decide) (choices 1) [1,2,128] r32775 c32775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16218
  · exact u16219
  · exact u16220

def r32776 : Route 9 := (fun mask => (mask,id))

def c32776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32776 : Upper (D 7) (R 7) [12,48,65,130,384] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130,384] 13 (by decide) (choices 1) [1,2,64] r32776 c32776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16221
  · exact u16222
  · exact u16223

def r32777 : Route 9 := (fun mask => (mask,id))

def c32777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32777 : Upper (D 7) (R 7) [12,48,65,160,3] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,3] 13 (by decide) (choices 1) [2,64,128,256] r32777 c32777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16224
  · exact u16225
  · exact u16226
  · exact u16227

def b32778 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 50 69 168 81 418 450 386 386), lower := (rows 13 50 69 168 81 32 64 128 256), losses := [] }

theorem u32778 : Upper (D 7) (R 7) [12,48,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32779 : Route 9 := (fun mask => (mask,id))

def c32779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32779 : Upper (D 7) (R 7) [12,48,65,160,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,66] 13 (by decide) (choices 1) [1,2,128,256] r32779 c32779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16228
  · exact u16229
  · exact u16230
  · exact u16231

def b32780 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 69 168 145 354 322 450 322), lower := (rows 13 50 69 168 145 32 64 128 256), losses := [] }

theorem u32780 : Upper (D 7) (R 7) [12,48,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32781 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 168 146 355 323 451 323), lower := (rows 13 50 69 168 146 32 64 128 256), losses := [] }

theorem u32781 : Upper (D 7) (R 7) [12,48,65,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32782 : Route 9 := (fun mask => (mask,id))

def c32782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32782 : Upper (D 7) (R 7) [12,48,65,160,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,192] 13 (by decide) (choices 1) [1,2,256] r32782 c32782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16232
  · exact u16233
  · exact u16234

def r32783 : Route 9 := (fun mask => (mask,id))

def c32783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32783 : Upper (D 7) (R 7) [12,48,65,160,257] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,257] 13 (by decide) (choices 1) [2,64,128] r32783 c32783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16235
  · exact u16236
  · exact u16237

def r32784 : Route 9 := (fun mask => (mask,id))

def c32784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32784 : Upper (D 7) (R 7) [12,48,65,160,258] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,258] 13 (by decide) (choices 1) [1,2,64,128] r32784 c32784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16238
  · exact u16239
  · exact u16240
  · exact u16241

def r32785 : Route 9 := (fun mask => (mask,id))

def c32785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32785 : Upper (D 7) (R 7) [12,48,65,160,320] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,320] 13 (by decide) (choices 1) [1,2,128] r32785 c32785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16242
  · exact u16243
  · exact u16244

def r32786 : Route 9 := (fun mask => (mask,id))

def c32786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32786 : Upper (D 7) (R 7) [12,48,65,160,384] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,384] 13 (by decide) (choices 1) [1,2,64] r32786 c32786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16245
  · exact u16246
  · exact u16247

def b32787 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 265 50 226 194 194 450), lower := (rows 13 50 69 265 50 32 64 128 256), losses := [] }

theorem u32787 : Upper (D 7) (R 7) [12,48,65,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32788 : Route 9 := (fun mask => (mask,id))

def c32788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32788 : Upper (D 7) (R 7) [12,48,65,257,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,257,66] 13 (by decide) (choices 1) [2,128] r32788 c32788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16248
  · exact u16249

def b32789 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 265 112 162 194 130 386), lower := (rows 13 50 69 265 112 32 64 128 256), losses := [] }

theorem u32789 : Upper (D 7) (R 7) [12,48,65,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32790 : Route 9 := (fun mask => (mask,id))

def c32790 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32790 : Upper (D 7) (R 7) [12,48,65,257,130] 13 := by
  apply FastRouting.sound _ _ [12,48,65,257,130] 13 (by decide) (choices 1) [2,64,128] r32790 c32790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16250
  · exact u16251
  · exact u16252

def b32791 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 265 176 226 194 194 450), lower := (rows 13 50 69 265 176 32 64 128 256), losses := [] }

theorem u32791 : Upper (D 7) (R 7) [12,48,65,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32792 : Route 9 := (fun mask => (mask,id))

def c32792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32792 : Upper (D 7) (R 7) [12,48,65,257,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,257,192] 13 (by decide) (choices 1) [2,128] r32792 c32792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16253
  · exact u16254

def b32793 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 13 50 69 266 19 224 224 224 480), lower := (rows 13 50 69 266 19 32 64 128 256), losses := [] }

theorem u32793 : Upper (D 7) (R 7) [12,48,65,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32794 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 266 49 226 194 194 450), lower := (rows 13 50 69 266 49 32 64 128 256), losses := [] }

theorem u32794 : Upper (D 7) (R 7) [12,48,65,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32795 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 266 50 225 193 193 449), lower := (rows 13 50 69 266 50 32 64 128 256), losses := [] }

theorem u32795 : Upper (D 7) (R 7) [12,48,65,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32796 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 50 69 266 81 162 226 162 418), lower := (rows 13 50 69 266 81 32 64 128 256), losses := [] }

theorem u32796 : Upper (D 7) (R 7) [12,48,65,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32797 : Route 9 := (fun mask => (mask,id))

def c32797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32797 : Upper (D 7) (R 7) [12,48,65,258,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,66] 13 (by decide) (choices 1) [1,128] r32797 c32797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16255
  · exact u16256

def b32798 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 266 112 163 195 131 387), lower := (rows 13 50 69 266 112 32 64 128 256), losses := [] }

theorem u32798 : Upper (D 7) (R 7) [12,48,65,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32799 : Route 9 := (fun mask => (mask,id))

def c32799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32799 : Upper (D 7) (R 7) [12,48,65,258,129] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,129] 13 (by decide) (choices 1) [2,64,128] r32799 c32799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16257
  · exact u16258
  · exact u16259

def r32800 : Route 9 := (fun mask => (mask,id))

def c32800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32800 : Upper (D 7) (R 7) [12,48,65,258,130] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,130] 13 (by decide) (choices 1) [1,64,128] r32800 c32800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16260
  · exact u16261
  · exact u16262

def b32801 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 266 176 227 195 195 451), lower := (rows 13 50 69 266 176 32 64 128 256), losses := [] }

theorem u32801 : Upper (D 7) (R 7) [12,48,65,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32802 : Route 9 := (fun mask => (mask,id))

def c32802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32802 : Upper (D 7) (R 7) [12,48,65,258,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,192] 13 (by decide) (choices 1) [1,2,128] r32802 c32802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16263
  · exact u16264
  · exact u16265

def r32803 : Route 9 := (fun mask => (mask,id))

def c32803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32803 : Upper (D 7) (R 7) [12,48,65,288,3] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,3] 13 (by decide) (choices 1) [2,64,128] r32803 c32803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16266
  · exact u16267
  · exact u16268

def b32804 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 50 69 296 81 162 194 130 386), lower := (rows 13 50 69 296 81 32 64 128 256), losses := [] }

theorem u32804 : Upper (D 7) (R 7) [12,48,65,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32805 : Route 9 := (fun mask => (mask,id))

def c32805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32805 : Upper (D 7) (R 7) [12,48,65,288,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,66] 13 (by decide) (choices 1) [1,2,128] r32805 c32805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16269
  · exact u16270
  · exact u16271

def r32806 : Route 9 := (fun mask => (mask,id))

def c32806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32806 : Upper (D 7) (R 7) [12,48,65,288,129] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,129] 13 (by decide) (choices 1) [2,64,128] r32806 c32806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16272
  · exact u16273
  · exact u16274

def r32807 : Route 9 := (fun mask => (mask,id))

def c32807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32807 : Upper (D 7) (R 7) [12,48,65,288,130] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,130] 13 (by decide) (choices 1) [1,2,64,128] r32807 c32807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16275
  · exact u16276
  · exact u16277
  · exact u16278

def r32808 : Route 9 := (fun mask => (mask,id))

def c32808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32808 : Upper (D 7) (R 7) [12,48,65,288,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,192] 13 (by decide) (choices 1) [1,2,128] r32808 c32808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16279
  · exact u16280
  · exact u16281

def r32809 : Route 9 := (fun mask => (mask,id))

def c32809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32809 : Upper (D 7) (R 7) [12,48,65,384,3] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,3] 13 (by decide) (choices 1) [2,64,128] r32809 c32809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16282
  · exact u16283
  · exact u16284

def b32810 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 392 49 226 194 194 450), lower := (rows 13 50 69 392 49 32 64 128 256), losses := [] }

theorem u32810 : Upper (D 7) (R 7) [12,48,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32811 : PairBound 9 := { available := 195, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 392 50 227 195 195 451), lower := (rows 13 50 69 392 50 32 64 128 256), losses := [] }

theorem u32811 : Upper (D 7) (R 7) [12,48,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32812 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 50 69 392 81 162 226 162 418), lower := (rows 13 50 69 392 81 32 64 128 256), losses := [] }

theorem u32812 : Upper (D 7) (R 7) [12,48,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32813 : Route 9 := (fun mask => (mask,id))

def c32813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32813 : Upper (D 7) (R 7) [12,48,65,384,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,66] 13 (by decide) (choices 1) [1,2,128] r32813 c32813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16285
  · exact u16286
  · exact u16287

def b32814 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 392 112 163 195 131 387), lower := (rows 13 50 69 392 112 32 64 128 256), losses := [] }

theorem u32814 : Upper (D 7) (R 7) [12,48,65,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32815 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 69 392 145 98 98 226 354), lower := (rows 13 50 69 392 145 32 64 128 256), losses := [] }

theorem u32815 : Upper (D 7) (R 7) [12,48,65,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32816 : Route 9 := (fun mask => (mask,id))

def c32816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32816 : Upper (D 7) (R 7) [12,48,65,384,130] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,130] 13 (by decide) (choices 1) [1,2,64] r32816 c32816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16288
  · exact u16289
  · exact u16290

def b32817 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 392 176 99 67 195 323), lower := (rows 13 50 69 392 176 32 64 128 256), losses := [] }

theorem u32817 : Upper (D 7) (R 7) [12,48,65,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32818 : Route 9 := (fun mask => (mask,id))

def c32818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32818 : Upper (D 7) (R 7) [12,48,65,384,192] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,192] 13 (by decide) (choices 1) [1,2] r32818 c32818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16291
  · exact u16292

def b32819 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 104 19 417 449 385 385), lower := (rows 13 50 70 104 19 32 64 128 256), losses := [] }

theorem u32819 : Upper (D 7) (R 7) [12,48,66,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32819
end Delivery.IrregularNine14.P07
