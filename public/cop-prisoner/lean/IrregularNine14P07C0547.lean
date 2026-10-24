import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0271
import IrregularNine14P07C0272

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32820 : Route 9 := (fun mask => (mask,id))

def c32820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32820 : Upper (D 7) (R 7) [12,48,66,96,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96,129] 13 (by decide) (choices 1) [1,2,128,256] r32820 c32820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16293
  · exact u16294
  · exact u16295
  · exact u16296

def b32821 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 104 146 417 449 385 385), lower := (rows 13 50 70 104 146 32 64 128 256), losses := [] }

theorem u32821 : Upper (D 7) (R 7) [12,48,66,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32822 : Route 9 := (fun mask => (mask,id))

def c32822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32822 : Upper (D 7) (R 7) [12,48,66,96,257] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96,257] 13 (by decide) (choices 1) [1,2,128] r32822 c32822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16297
  · exact u16298
  · exact u16299

def b32823 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 104 274 161 193 129 385), lower := (rows 13 50 70 104 274 32 64 128 256), losses := [] }

theorem u32823 : Upper (D 7) (R 7) [12,48,66,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32824 : Route 9 := (fun mask => (mask,id))

def c32824 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32824 : Upper (D 7) (R 7) [12,48,66,96,384] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96,384] 13 (by decide) (choices 1) [1,2,128] r32824 c32824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16300
  · exact u16301
  · exact u16302

def b32825 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 138 49 481 449 449 449), lower := (rows 13 50 70 138 49 32 64 128 256), losses := [] }

theorem u32825 : Upper (D 7) (R 7) [12,48,66,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32826 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 0, region := 496, targets := 2 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,1)], upper := (rows 13 50 70 138 81 417 481 417 417), lower := (rows 13 50 70 138 81 32 64 128 256), losses := [] }

theorem u32826 : Upper (D 7) (R 7) [12,48,66,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32827 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 6, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 138 112 417 449 385 385), lower := (rows 13 50 70 138 112 32 64 128 256), losses := [] }

theorem u32827 : Upper (D 7) (R 7) [12,48,66,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32828 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(3,6)], upper := (rows 13 50 70 138 208 289 353 417 289), lower := (rows 13 50 70 138 208 32 64 128 256), losses := [] }

theorem u32828 : Upper (D 7) (R 7) [12,48,66,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m32829_128 : Upper (D 7) (R 7) [12,48,66,130,257,128] 13 :=
  permutation_upper _ _ _ [12,48,66,130,257,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16304

def r32829 : Route 9 := (fun mask => (mask,id))

def c32829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32829 : Upper (D 7) (R 7) [12,48,66,130,257] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130,257] 13 (by decide) (choices 1) [1,64,128] r32829 c32829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16303
  · exact u16304
  · exact m32829_128

def b32830 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 138 304 225 193 193 449), lower := (rows 13 50 70 138 304 32 64 128 256), losses := [] }

theorem u32830 : Upper (D 7) (R 7) [12,48,66,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32831 : Route 9 := (fun mask => (mask,id))

def c32831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32831 : Upper (D 7) (R 7) [12,48,66,130,320] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130,320] 13 (by decide) (choices 1) [1,128] r32831 c32831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16305
  · exact u16306

def r32832 : Route 9 := (fun mask => (mask,id))

def c32832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32832 : Upper (D 7) (R 7) [12,48,66,160,3] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,3] 13 (by decide) (choices 1) [1,64,128,256] r32832 c32832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16307
  · exact u16308
  · exact u16309
  · exact u16310

def r32833 : Route 9 := (fun mask => (mask,id))

def c32833 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32833 : Upper (D 7) (R 7) [12,48,66,160,65] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,65] 13 (by decide) (choices 1) [1,2,128,256] r32833 c32833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16311
  · exact u16312
  · exact u16313
  · exact u16314

def b32834 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 50 70 168 82 417 449 385 385), lower := (rows 13 50 70 168 82 32 64 128 256), losses := [] }

theorem u32834 : Upper (D 7) (R 7) [12,48,66,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32835 : Route 9 := (fun mask => (mask,id))

def c32835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32835 : Upper (D 7) (R 7) [12,48,66,160,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,129] 13 (by decide) (choices 1) [1,2,64,256] r32835 c32835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16315
  · exact u16316
  · exact u16317
  · exact u16318

def b32836 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 168 146 353 321 449 321), lower := (rows 13 50 70 168 146 32 64 128 256), losses := [] }

theorem u32836 : Upper (D 7) (R 7) [12,48,66,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32837 : Route 9 := (fun mask => (mask,id))

def c32837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32837 : Upper (D 7) (R 7) [12,48,66,160,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,192] 13 (by decide) (choices 1) [1,2,256] r32837 c32837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16319
  · exact u16320
  · exact u16321

def r32838 : Route 9 := (fun mask => (mask,id))

def c32838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32838 : Upper (D 7) (R 7) [12,48,66,160,257] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,257] 13 (by decide) (choices 1) [1,2,64,128] r32838 c32838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16322
  · exact u16323
  · exact u16324
  · exact u16325

def r32839 : Route 9 := (fun mask => (mask,id))

def c32839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32839 : Upper (D 7) (R 7) [12,48,66,160,258] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,258] 13 (by decide) (choices 1) [1,64,128] r32839 c32839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16326
  · exact u16327
  · exact u16328

def r32840 : Route 9 := (fun mask => (mask,id))

def c32840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32840 : Upper (D 7) (R 7) [12,48,66,160,320] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,320] 13 (by decide) (choices 1) [1,2,128] r32840 c32840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16329
  · exact u16330
  · exact u16331

def r32841 : Route 9 := (fun mask => (mask,id))

def c32841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32841 : Upper (D 7) (R 7) [12,48,66,160,384] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,384] 13 (by decide) (choices 1) [1,2,64] r32841 c32841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16332
  · exact u16333
  · exact u16334

def b32842 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 200 19 417 481 417 417), lower := (rows 13 50 70 200 19 32 64 128 256), losses := [] }

theorem u32842 : Upper (D 7) (R 7) [12,48,66,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32843 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 50 70 200 49 419 451 387 387), lower := (rows 13 50 70 200 49 32 64 128 256), losses := [] }

theorem u32843 : Upper (D 7) (R 7) [12,48,66,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32844 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 70 200 50 417 449 385 385), lower := (rows 13 50 70 200 50 32 64 128 256), losses := [] }

theorem u32844 : Upper (D 7) (R 7) [12,48,66,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32845 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 50 70 200 145 291 355 419 291), lower := (rows 13 50 70 200 145 32 64 128 256), losses := [] }

theorem u32845 : Upper (D 7) (R 7) [12,48,66,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32846 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 200 146 289 353 417 289), lower := (rows 13 50 70 200 146 32 64 128 256), losses := [] }

theorem u32846 : Upper (D 7) (R 7) [12,48,66,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32847 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 200 176 291 323 387 259), lower := (rows 13 50 70 200 176 32 64 128 256), losses := [] }

theorem u32847 : Upper (D 7) (R 7) [12,48,66,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32848 : Route 9 := (fun mask => (mask,id))

def c32848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32848 : Upper (D 7) (R 7) [12,48,66,192,257] 13 := by
  apply FastRouting.sound _ _ [12,48,66,192,257] 13 (by decide) (choices 1) [1,2,128] r32848 c32848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16335
  · exact u16336
  · exact u16337

def b32849 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 200 274 161 225 161 417), lower := (rows 13 50 70 200 274 32 64 128 256), losses := [] }

theorem u32849 : Upper (D 7) (R 7) [12,48,66,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32850 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 200 304 163 195 131 387), lower := (rows 13 50 70 200 304 32 64 128 256), losses := [] }

theorem u32850 : Upper (D 7) (R 7) [12,48,66,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32851 : Route 9 := (fun mask => (mask,id))

def c32851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32851 : Upper (D 7) (R 7) [12,48,66,192,384] 13 := by
  apply FastRouting.sound _ _ [12,48,66,192,384] 13 (by decide) (choices 1) [1,2] r32851 c32851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16338
  · exact u16339

def b32852 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(3,1)], upper := (rows 13 50 70 265 19 224 224 224 480), lower := (rows 13 50 70 265 19 32 64 128 256), losses := [] }

theorem u32852 : Upper (D 7) (R 7) [12,48,66,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32853 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 265 49 226 194 194 450), lower := (rows 13 50 70 265 49 32 64 128 256), losses := [] }

theorem u32853 : Upper (D 7) (R 7) [12,48,66,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32854 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 70 265 50 225 193 193 449), lower := (rows 13 50 70 265 50 32 64 128 256), losses := [] }

theorem u32854 : Upper (D 7) (R 7) [12,48,66,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32855 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 166, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 13 50 70 265 81 162 226 162 418), lower := (rows 13 50 70 265 81 32 64 128 256), losses := [] }

theorem u32855 : Upper (D 7) (R 7) [12,48,66,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32856 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 50 70 265 82 161 225 161 417), lower := (rows 13 50 70 265 82 32 64 128 256), losses := [] }

theorem u32856 : Upper (D 7) (R 7) [12,48,66,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32857 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 6, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 265 112 163 195 131 387), lower := (rows 13 50 70 265 112 32 64 128 256), losses := [] }

theorem u32857 : Upper (D 7) (R 7) [12,48,66,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32858 : Route 9 := (fun mask => (mask,id))

def c32858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32858 : Upper (D 7) (R 7) [12,48,66,257,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,257,129] 13 (by decide) (choices 1) [2,64,128] r32858 c32858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16340
  · exact u16341
  · exact u16342

def r32859 : Route 9 := (fun mask => (mask,id))

def c32859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32859 : Upper (D 7) (R 7) [12,48,66,257,130] 13 := by
  apply FastRouting.sound _ _ [12,48,66,257,130] 13 (by decide) (choices 1) [1,64,128] r32859 c32859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16343
  · exact u16344
  · exact u16345

def b32860 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 265 176 227 195 195 451), lower := (rows 13 50 70 265 176 32 64 128 256), losses := [] }

theorem u32860 : Upper (D 7) (R 7) [12,48,66,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32861 : Route 9 := (fun mask => (mask,id))

def c32861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32861 : Upper (D 7) (R 7) [12,48,66,257,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,257,192] 13 (by decide) (choices 1) [1,2,128] r32861 c32861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16346
  · exact u16347
  · exact u16348

def b32862 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 266 49 225 193 193 449), lower := (rows 13 50 70 266 49 32 64 128 256), losses := [] }

theorem u32862 : Upper (D 7) (R 7) [12,48,66,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32863 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 162, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,1)], upper := (rows 13 50 70 266 81 161 225 161 417), lower := (rows 13 50 70 266 81 32 64 128 256), losses := [] }

theorem u32863 : Upper (D 7) (R 7) [12,48,66,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32864 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 6, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 266 112 161 193 129 385), lower := (rows 13 50 70 266 112 32 64 128 256), losses := [] }

theorem u32864 : Upper (D 7) (R 7) [12,48,66,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32865 : Route 9 := (fun mask => (mask,id))

def c32865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32865 : Upper (D 7) (R 7) [12,48,66,258,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,258,129] 13 (by decide) (choices 1) [1,64,128] r32865 c32865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16349
  · exact u16350
  · exact u16351

def b32866 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 266 176 225 193 193 449), lower := (rows 13 50 70 266 176 32 64 128 256), losses := [] }

theorem u32866 : Upper (D 7) (R 7) [12,48,66,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32867 : Route 9 := (fun mask => (mask,id))

def c32867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32867 : Upper (D 7) (R 7) [12,48,66,258,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,258,192] 13 (by decide) (choices 1) [1,128] r32867 c32867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16352
  · exact u16353

def r32868 : Route 9 := (fun mask => (mask,id))

def c32868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32868 : Upper (D 7) (R 7) [12,48,66,288,3] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,3] 13 (by decide) (choices 1) [1,64,128] r32868 c32868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16354
  · exact u16355
  · exact u16356

def r32869 : Route 9 := (fun mask => (mask,id))

def c32869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32869 : Upper (D 7) (R 7) [12,48,66,288,65] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,65] 13 (by decide) (choices 1) [1,2,128] r32869 c32869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16357
  · exact u16358
  · exact u16359

def b32870 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 50 70 296 82 161 193 129 385), lower := (rows 13 50 70 296 82 32 64 128 256), losses := [] }

theorem u32870 : Upper (D 7) (R 7) [12,48,66,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32871 : Route 9 := (fun mask => (mask,id))

def c32871 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32871 : Upper (D 7) (R 7) [12,48,66,288,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,129] 13 (by decide) (choices 1) [1,2,64,128] r32871 c32871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16360
  · exact u16361
  · exact u16362
  · exact u16363

def r32872 : Route 9 := (fun mask => (mask,id))

def c32872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32872 : Upper (D 7) (R 7) [12,48,66,288,130] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,130] 13 (by decide) (choices 1) [1,64,128] r32872 c32872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16364
  · exact u16365
  · exact u16366

def r32873 : Route 9 := (fun mask => (mask,id))

def c32873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32873 : Upper (D 7) (R 7) [12,48,66,288,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,192] 13 (by decide) (choices 1) [1,2,128] r32873 c32873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16367
  · exact u16368
  · exact u16369

def b32874 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 328 19 161 225 161 417), lower := (rows 13 50 70 328 19 32 64 128 256), losses := [] }

theorem u32874 : Upper (D 7) (R 7) [12,48,66,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32875 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 50 70 328 49 163 195 131 387), lower := (rows 13 50 70 328 49 32 64 128 256), losses := [] }

theorem u32875 : Upper (D 7) (R 7) [12,48,66,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32876 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 70 328 50 161 193 129 385), lower := (rows 13 50 70 328 50 32 64 128 256), losses := [] }

theorem u32876 : Upper (D 7) (R 7) [12,48,66,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32877 : Route 9 := (fun mask => (mask,id))

def c32877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32877 : Upper (D 7) (R 7) [12,48,66,320,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,320,129] 13 (by decide) (choices 1) [1,2,128] r32877 c32877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16370
  · exact u16371
  · exact u16372

def b32878 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 328 146 161 225 161 417), lower := (rows 13 50 70 328 146 32 64 128 256), losses := [] }

theorem u32878 : Upper (D 7) (R 7) [12,48,66,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32879 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 328 176 163 195 131 387), lower := (rows 13 50 70 328 176 32 64 128 256), losses := [] }

theorem u32879 : Upper (D 7) (R 7) [12,48,66,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32879
end Delivery.IrregularNine14.P07
