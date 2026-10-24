import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0072
import IrregularNine14P06C0073

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16860 : Route 9 := (fun mask => (mask,id))

def c16860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16860 : Upper (D 6) (R 6) [10,144,96,288,5,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,5,2] 13 (by decide) (choices 1) [1,4] r16860 c16860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4351
  · exact u4352

def b16861 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 11 146 100 296 21 36 67 195 323), lower := (rows 11 146 100 296 21 36 64 128 256), losses := [] }

theorem u16861 : Upper (D 6) (R 6) [10,144,96,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16862 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 296 21 96 71 135 263), lower := (rows 11 146 100 296 21 96 64 128 256), losses := [] }

theorem u16862 : Upper (D 6) (R 6) [10,144,96,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16863 : Route 9 := (fun mask => (mask,id))

def c16863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16863 : Upper (D 6) (R 6) [10,144,96,288,6,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,6,1] 13 (by decide) (choices 1) [1,4] r16863 c16863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4353
  · exact u4354

def b16864 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 296 22 36 65 193 321), lower := (rows 11 146 100 296 22 36 64 128 256), losses := [] }

theorem u16864 : Upper (D 6) (R 6) [10,144,96,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16865 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 296 22 96 69 133 261), lower := (rows 11 146 100 296 22 96 64 128 256), losses := [] }

theorem u16865 : Upper (D 6) (R 6) [10,144,96,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16866 : Route 9 := (fun mask => (mask,id))

def c16866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16866 : Upper (D 6) (R 6) [10,144,96,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,65,1] 13 (by decide) (choices 1) [2,4] r16866 c16866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4355
  · exact u4356

def r16867 : Route 9 := (fun mask => (mask,id))

def c16867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16867 : Upper (D 6) (R 6) [10,144,96,288,65,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,65,2] 13 (by decide) (choices 1) [1,4] r16867 c16867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4357
  · exact u4358

def r16868 : Route 9 := (fun mask => (mask,id))

def c16868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16868 : Upper (D 6) (R 6) [10,144,96,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,65,4] 13 (by decide) (choices 1) [1,2,4] r16868 c16868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4359
  · exact u4360
  · exact u4361

def r16869 : Route 9 := (fun mask => (mask,id))

def c16869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16869 : Upper (D 6) (R 6) [10,144,96,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,66,1] 13 (by decide) (choices 1) [1,4] r16869 c16869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4362
  · exact u4363

def b16870 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 296 82 36 69 133 261), lower := (rows 11 146 100 296 82 36 64 128 256), losses := [] }

theorem u16870 : Upper (D 6) (R 6) [10,144,96,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16871 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 261 41 84 34 100 228 356), lower := (rows 11 146 261 41 84 34 64 128 256), losses := [] }

theorem u16871 : Upper (D 6) (R 6) [10,144,257,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16872 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 261 41 84 36 98 226 354), lower := (rows 11 146 261 41 84 36 64 128 256), losses := [] }

theorem u16872 : Upper (D 6) (R 6) [10,144,257,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16873 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 146 261 41 84 96 102 166 294), lower := (rows 11 146 261 41 84 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 11 187 257 41 112 96 96 128 256) }] }

theorem u16873 : Upper (D 6) (R 6) [10,144,257,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16874 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 324, targets := 34 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(2,5),(4,2)], upper := (rows 11 146 261 44 49 34 68 196 324), lower := (rows 11 146 261 44 49 34 64 128 256), losses := [] }

theorem u16874 : Upper (D 6) (R 6) [10,144,257,36,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16875 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 146 261 44 49 36 66 194 322), lower := (rows 11 146 261 44 49 36 64 128 256), losses := [] }

theorem u16875 : Upper (D 6) (R 6) [10,144,257,36,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16876 : Route 9 := (fun mask => (mask,id))

def c16876 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16876 : Upper (D 6) (R 6) [10,144,257,36,33,64] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,33,64] 13 (by decide) (choices 1) [2,4] r16876 c16876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4364
  · exact u4365

def b16877 : PairBound 9 := { available := 100, camps := [], pairs := [(2,1),(3,0),(4,1)], upper := (rows 11 146 261 44 81 34 100 228 356), lower := (rows 11 146 261 44 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 35 76 140 268), good := (rows 490 178 492 492 112 34 64 128 256) },{ target := 1, region := (rows 1 0 5 8 17 32 72 136 264), good := (rows 477 144 277 492 85 32 64 128 256) }] }

theorem u16877 : Upper (D 6) (R 6) [10,144,257,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16878 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 261 44 81 36 98 226 354), lower := (rows 11 146 261 44 81 36 64 128 256), losses := [] }

theorem u16878 : Upper (D 6) (R 6) [10,144,257,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16879 : Route 9 := (fun mask => (mask,id))

def c16879 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16879 : Upper (D 6) (R 6) [10,144,257,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,65,64] 13 (by decide) (choices 1) [2,4,32] r16879 c16879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4366
  · exact u4367
  · exact u4368

def b16880 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 261 44 82 33 100 228 356), lower := (rows 11 146 261 44 82 33 64 128 256), losses := [] }

theorem u16880 : Upper (D 6) (R 6) [10,144,257,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16881 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 261 44 82 36 97 225 353), lower := (rows 11 146 261 44 82 36 64 128 256), losses := [] }

theorem u16881 : Upper (D 6) (R 6) [10,144,257,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16882 : Route 9 := (fun mask => (mask,id))

def c16882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16882 : Upper (D 6) (R 6) [10,144,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,66,64] 13 (by decide) (choices 1) [1,4,32] r16882 c16882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4369
  · exact u4370
  · exact u4371

def b16883 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 11 146 261 44 84 33 98 226 354), lower := (rows 11 146 261 44 84 33 64 128 256), losses := [] }

theorem u16883 : Upper (D 6) (R 6) [10,144,257,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16884 : PairBound 9 := { available := 97, camps := [], pairs := [(1,2),(3,0),(3,6)], upper := (rows 11 146 261 44 84 34 97 225 353), lower := (rows 11 146 261 44 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 35 64 128 256), good := (rows 42 178 300 44 92 34 64 128 256) },{ target := 2, region := (rows 1 18 0 8 16 51 69 133 261), good := (rows 491 178 481 488 498 34 64 128 256) },{ target := 6, region := (rows 1 2 4 12 16 35 0 128 256), good := (rows 43 178 301 44 28 34 0 128 256) }] }

theorem u16884 : Upper (D 6) (R 6) [10,144,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16885 : Route 9 := (fun mask => (mask,id))

def c16885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16885 : Upper (D 6) (R 6) [10,144,257,36,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,68,64] 13 (by decide) (choices 1) [1,2,32] r16885 c16885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4372
  · exact u4373
  · exact u4374

def b16886 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 11 146 261 44 112 33 70 198 326), lower := (rows 11 146 261 44 112 33 64 128 256), losses := [] }

theorem u16886 : Upper (D 6) (R 6) [10,144,257,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16887 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 34 }], pairs := [(2,1),(2,5),(3,0)], upper := (rows 11 146 261 44 112 34 69 197 325), lower := (rows 11 146 261 44 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 35 64 128 256), good := (rows 42 178 300 44 112 34 64 128 256) }] }

theorem u16887 : Upper (D 6) (R 6) [10,144,257,36,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16888 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 261 44 112 36 67 195 323), lower := (rows 11 146 261 44 112 36 64 128 256), losses := [] }

theorem u16888 : Upper (D 6) (R 6) [10,144,257,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16889 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 261 44 112 96 71 135 263), lower := (rows 11 146 261 44 112 96 64 128 256), losses := [] }

theorem u16889 : Upper (D 6) (R 6) [10,144,257,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16890 : Route 9 := (fun mask => (mask,id))

def c16890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16890 : Upper (D 6) (R 6) [10,144,257,96,6,1] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96,6,1] 13 (by decide) (choices 1) [4,32] r16890 c16890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4375
  · exact u4376

theorem m16891_1 : Upper (D 6) (R 6) [10,144,257,96,6,4,1] 13 :=
  permutation_upper _ _ _ [10,144,257,96,6,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4375

def r16891 : Route 9 := (fun mask => (mask,id))

def c16891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16891 : Upper (D 6) (R 6) [10,144,257,96,6,4] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96,6,4] 13 (by decide) (choices 1) [1,32] r16891 c16891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16891_1
  · exact u4377

def b16892 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 261 104 22 96 101 165 293), lower := (rows 11 146 261 104 22 96 64 128 256), losses := [] }

theorem u16892 : Upper (D 6) (R 6) [10,144,257,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16893 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 324, targets := 34 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(2,5),(4,2)], upper := (rows 11 146 261 104 49 34 68 196 324), lower := (rows 11 146 261 104 49 34 64 128 256), losses := [] }

theorem u16893 : Upper (D 6) (R 6) [10,144,257,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16894 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 146 261 104 49 36 70 198 326), lower := (rows 11 146 261 104 49 36 64 128 256), losses := [] }

theorem u16894 : Upper (D 6) (R 6) [10,144,257,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16895 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 261 104 49 96 70 134 262), lower := (rows 11 146 261 104 49 96 64 128 256), losses := [] }

theorem u16895 : Upper (D 6) (R 6) [10,144,257,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16896 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 146 261 104 52 33 70 198 326), lower := (rows 11 146 261 104 52 33 64 128 256), losses := [] }

theorem u16896 : Upper (D 6) (R 6) [10,144,257,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16897 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 34 }], pairs := [(2,1),(2,5),(4,0)], upper := (rows 11 146 261 104 52 34 69 197 325), lower := (rows 11 146 261 104 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 35 64 128 256), good := (rows 42 178 308 104 52 34 64 128 256) }] }

theorem u16897 : Upper (D 6) (R 6) [10,144,257,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16898 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 261 104 52 36 67 195 323), lower := (rows 11 146 261 104 52 36 64 128 256), losses := [] }

theorem u16898 : Upper (D 6) (R 6) [10,144,257,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16899 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 261 104 52 96 71 135 263), lower := (rows 11 146 261 104 52 96 64 128 256), losses := [] }

theorem u16899 : Upper (D 6) (R 6) [10,144,257,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16900 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 262 41 52 33 68 196 324), lower := (rows 11 146 262 41 52 33 64 128 256), losses := [] }

theorem u16900 : Upper (D 6) (R 6) [10,144,258,33,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16901 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 146 262 41 52 36 65 193 321), lower := (rows 11 146 262 41 52 36 64 128 256), losses := [] }

theorem u16901 : Upper (D 6) (R 6) [10,144,258,33,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16902 : Route 9 := (fun mask => (mask,id))

def c16902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16902 : Upper (D 6) (R 6) [10,144,258,33,36,64] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,36,64] 13 (by decide) (choices 1) [1,4] r16902 c16902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4378
  · exact u4379

def b16903 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 146 262 41 81 36 100 228 356), lower := (rows 11 146 262 41 81 36 64 128 256), losses := [] }

theorem u16903 : Upper (D 6) (R 6) [10,144,258,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16904 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 262 41 81 96 100 164 292), lower := (rows 11 146 262 41 81 96 64 128 256), losses := [] }

theorem u16904 : Upper (D 6) (R 6) [10,144,258,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16905 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 262 41 84 33 100 228 356), lower := (rows 11 146 262 41 84 33 64 128 256), losses := [] }

theorem u16905 : Upper (D 6) (R 6) [10,144,258,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16906 : Route 9 := (fun mask => (mask,id))

def c16906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16906 : Upper (D 6) (R 6) [10,144,258,33,68,4] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,68,4] 13 (by decide) (choices 1) [1,32] r16906 c16906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4380
  · exact u4381

def b16907 : PairBound 9 := { available := 37, camps := [], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 146 262 41 84 96 101 165 293), lower := (rows 11 146 262 41 84 96 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 26 16 112 64 128 256), good := (rows 11 187 267 41 121 96 96 128 256) },{ target := 6, region := (rows 1 2 5 8 16 32 0 136 264), good := (rows 399 146 262 429 20 32 0 128 256) }] }

theorem u16907 : Upper (D 6) (R 6) [10,144,258,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16908 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 262 41 112 33 68 196 324), lower := (rows 11 146 262 41 112 33 64 128 256), losses := [] }

theorem u16908 : Upper (D 6) (R 6) [10,144,258,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16909 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 11 146 262 41 112 36 69 197 325), lower := (rows 11 146 262 41 112 36 64 128 256), losses := [] }

theorem u16909 : Upper (D 6) (R 6) [10,144,258,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16910 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 262 41 112 96 69 133 261), lower := (rows 11 146 262 41 112 96 64 128 256), losses := [] }

theorem u16910 : Upper (D 6) (R 6) [10,144,258,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16911 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 146 262 44 21 33 96 224 352), lower := (rows 11 146 262 44 21 33 64 128 256), losses := [] }

theorem u16911 : Upper (D 6) (R 6) [10,144,258,36,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16912 : Route 9 := (fun mask => (mask,id))

def c16912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16912 : Upper (D 6) (R 6) [10,144,258,36,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,5,64] 13 (by decide) (choices 1) [1,32] r16912 c16912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4382
  · exact u4383

def b16913 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 146 262 44 49 33 68 196 324), lower := (rows 11 146 262 44 49 33 64 128 256), losses := [] }

theorem u16913 : Upper (D 6) (R 6) [10,144,258,36,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16914 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 146 262 44 49 36 65 193 321), lower := (rows 11 146 262 44 49 36 64 128 256), losses := [] }

theorem u16914 : Upper (D 6) (R 6) [10,144,258,36,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16915 : Route 9 := (fun mask => (mask,id))

def c16915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16915 : Upper (D 6) (R 6) [10,144,258,36,33,64] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,33,64] 13 (by decide) (choices 1) [1,4] r16915 c16915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4384
  · exact u4385

def b16916 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 262 44 81 33 100 228 356), lower := (rows 11 146 262 44 81 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 40 16 32 104 168 296), good := (rows 462 146 262 492 84 492 64 128 256) }] }

theorem u16916 : Upper (D 6) (R 6) [10,144,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16917 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 262 44 81 36 97 225 353), lower := (rows 11 146 262 44 81 36 64 128 256), losses := [] }

theorem u16917 : Upper (D 6) (R 6) [10,144,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16918 : Route 9 := (fun mask => (mask,id))

def c16918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16918 : Upper (D 6) (R 6) [10,144,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,65,64] 13 (by decide) (choices 1) [1,4,32] r16918 c16918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4386
  · exact u4387
  · exact u4388

def b16919 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 146 262 44 84 33 97 225 353), lower := (rows 11 146 262 44 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 33 97 161 289), good := (rows 505 144 260 508 84 481 64 128 256) }] }

theorem u16919 : Upper (D 6) (R 6) [10,144,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16919
end Delivery.IrregularNine14.P06
