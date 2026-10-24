import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0092
import IrregularNine14P08C0093
import IrregularNine14P08C0094

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15840 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 274 180 244 180 436), lower := (rows 193 35 44 73 274 32 64 128 256), losses := [] }

theorem u15840 : Upper (D 8) (R 8) [192,33,40,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15841 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 276 178 242 178 434), lower := (rows 193 35 44 73 276 32 64 128 256), losses := [] }

theorem u15841 : Upper (D 8) (R 8) [192,33,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15842 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 304 182 214 150 406), lower := (rows 193 35 44 73 304 32 64 128 256), losses := [] }

theorem u15842 : Upper (D 8) (R 8) [192,33,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15843 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 400 54 118 182 310), lower := (rows 193 35 44 73 400 32 64 128 256), losses := [] }

theorem u15843 : Upper (D 8) (R 8) [192,33,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15844 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 145 308 372 436 308), lower := (rows 193 35 44 74 145 32 64 128 256), losses := [] }

theorem u15844 : Upper (D 8) (R 8) [192,33,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15845 : Route 9 := (fun mask => (mask,id))

def c15845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15845 : Upper (D 8) (R 8) [192,33,40,66,132] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,132] 13 (by decide) (choices 1) [1,16,256] r15845 c15845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5566
  · exact u5567
  · exact u5568

def r15846 : Route 9 := (fun mask => (mask,id))

def c15846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15846 : Upper (D 8) (R 8) [192,33,40,66,160] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,160] 13 (by decide) (choices 1) [1,4,16,256] r15846 c15846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5569
  · exact u5570
  · exact u5571
  · exact u5572

def r15847 : Route 9 := (fun mask => (mask,id))

def c15847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15847 : Upper (D 8) (R 8) [192,33,40,66,257] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,257] 13 (by decide) (choices 1) [4,16,128] r15847 c15847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5573
  · exact u5574
  · exact u5575

def r15848 : Route 9 := (fun mask => (mask,id))

def c15848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15848 : Upper (D 8) (R 8) [192,33,40,66,260] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,260] 13 (by decide) (choices 1) [1,16,128] r15848 c15848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5576
  · exact u5577
  · exact u5578

def r15849 : Route 9 := (fun mask => (mask,id))

def c15849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15849 : Upper (D 8) (R 8) [192,33,40,66,288] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,288] 13 (by decide) (choices 1) [1,4,16,128] r15849 c15849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5579
  · exact u5580
  · exact u5581
  · exact u5582

def r15850 : Route 9 := (fun mask => (mask,id))

def c15850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15850 : Upper (D 8) (R 8) [192,33,40,66,384] 13 := by
  apply FastRouting.sound _ _ [192,33,40,66,384] 13 (by decide) (choices 1) [1,4,16] r15850 c15850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5583
  · exact u5584
  · exact u5585

def b15851 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 146 305 369 433 305), lower := (rows 193 35 44 76 146 32 64 128 256), losses := [] }

theorem u15851 : Upper (D 8) (R 8) [192,33,40,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15852 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 176 307 339 403 275), lower := (rows 193 35 44 76 176 32 64 128 256), losses := [] }

theorem u15852 : Upper (D 8) (R 8) [192,33,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15853 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 273 178 242 178 434), lower := (rows 193 35 44 76 273 32 64 128 256), losses := [] }

theorem u15853 : Upper (D 8) (R 8) [192,33,40,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15854 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 274 177 241 177 433), lower := (rows 193 35 44 76 274 32 64 128 256), losses := [] }

theorem u15854 : Upper (D 8) (R 8) [192,33,40,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15855 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 304 179 211 147 403), lower := (rows 193 35 44 76 304 32 64 128 256), losses := [] }

theorem u15855 : Upper (D 8) (R 8) [192,33,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15856 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 76 400 51 115 179 307), lower := (rows 193 35 44 76 400 32 64 128 256), losses := [] }

theorem u15856 : Upper (D 8) (R 8) [192,33,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15857 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 88 145 294 358 422 294), lower := (rows 193 35 44 88 145 32 64 128 256), losses := [] }

theorem u15857 : Upper (D 8) (R 8) [192,33,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15858 : Route 9 := (fun mask => (mask,id))

def c15858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15858 : Upper (D 8) (R 8) [192,33,40,80,130] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,130] 13 (by decide) (choices 1) [1,4,256] r15858 c15858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5586
  · exact u5587
  · exact u5588

def b15859 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 290, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 88 148 291 355 419 291), lower := (rows 193 35 44 88 148 32 64 128 256), losses := [] }

theorem u15859 : Upper (D 8) (R 8) [192,33,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15860 : Route 9 := (fun mask => (mask,id))

def c15860 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15860 : Upper (D 8) (R 8) [192,33,40,80,160] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,160] 13 (by decide) (choices 1) [1,2,4,256] r15860 c15860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5589
  · exact u5590
  · exact u5591
  · exact u5592

def r15861 : Route 9 := (fun mask => (mask,id))

def c15861 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15861 : Upper (D 8) (R 8) [192,33,40,80,257] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,257] 13 (by decide) (choices 1) [2,4,128] r15861 c15861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5593
  · exact u5594
  · exact u5595

def r15862 : Route 9 := (fun mask => (mask,id))

def c15862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15862 : Upper (D 8) (R 8) [192,33,40,80,258] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,258] 13 (by decide) (choices 1) [1,4,128] r15862 c15862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5596
  · exact u5597
  · exact u5598

def b15863 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 88 276 163 227 163 419), lower := (rows 193 35 44 88 276 32 64 128 256), losses := [] }

theorem u15863 : Upper (D 8) (R 8) [192,33,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15864 : Route 9 := (fun mask => (mask,id))

def c15864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15864 : Upper (D 8) (R 8) [192,33,40,80,288] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,288] 13 (by decide) (choices 1) [1,2,4,128] r15864 c15864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5599
  · exact u5600
  · exact u5601
  · exact u5602

def r15865 : Route 9 := (fun mask => (mask,id))

def c15865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15865 : Upper (D 8) (R 8) [192,33,40,80,384] 13 := by
  apply FastRouting.sound _ _ [192,33,40,80,384] 13 (by decide) (choices 1) [1,2,4] r15865 c15865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5603
  · exact u5604
  · exact u5605

def b15866 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 146 309 341 405 277), lower := (rows 193 35 44 104 146 32 64 128 256), losses := [] }

theorem u15866 : Upper (D 8) (R 8) [192,33,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15867 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 148 307 339 403 275), lower := (rows 193 35 44 104 148 32 64 128 256), losses := [] }

theorem u15867 : Upper (D 8) (R 8) [192,33,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15868 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 273 182 214 150 406), lower := (rows 193 35 44 104 273 32 64 128 256), losses := [] }

theorem u15868 : Upper (D 8) (R 8) [192,33,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15869 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 274 181 213 149 405), lower := (rows 193 35 44 104 274 32 64 128 256), losses := [] }

theorem u15869 : Upper (D 8) (R 8) [192,33,40,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15870 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 276 179 211 147 403), lower := (rows 193 35 44 104 276 32 64 128 256), losses := [] }

theorem u15870 : Upper (D 8) (R 8) [192,33,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15871 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 104 400 55 87 151 279), lower := (rows 193 35 44 104 400 32 64 128 256), losses := [] }

theorem u15871 : Upper (D 8) (R 8) [192,33,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15872 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 35 44 200 273 54 118 182 310), lower := (rows 193 35 44 200 273 32 64 128 256), losses := [] }

theorem u15872 : Upper (D 8) (R 8) [192,33,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15873 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 35 44 200 274 53 117 181 309), lower := (rows 193 35 44 200 274 32 64 128 256), losses := [] }

theorem u15873 : Upper (D 8) (R 8) [192,33,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15874 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 35 44 200 276 51 115 179 307), lower := (rows 193 35 44 200 276 32 64 128 256), losses := [] }

theorem u15874 : Upper (D 8) (R 8) [192,33,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15875 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 35 44 200 304 55 87 151 279), lower := (rows 193 35 44 200 304 32 64 128 256), losses := [] }

theorem u15875 : Upper (D 8) (R 8) [192,33,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15876 : Route 9 := (fun mask => (mask,id))

def c15876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15876 : Upper (D 8) (R 8) [192,33,40,257,66] 13 := by
  apply FastRouting.sound _ _ [192,33,40,257,66] 13 (by decide) (choices 1) [4,16,128] r15876 c15876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5606
  · exact u5607
  · exact u5608

def r15877 : Route 9 := (fun mask => (mask,id))

def c15877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15877 : Upper (D 8) (R 8) [192,33,40,257,68] 13 := by
  apply FastRouting.sound _ _ [192,33,40,257,68] 13 (by decide) (choices 1) [2,16,128] r15877 c15877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5609
  · exact u5610
  · exact u5611

def r15878 : Route 9 := (fun mask => (mask,id))

def c15878 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15878 : Upper (D 8) (R 8) [192,33,40,257,96] 13 := by
  apply FastRouting.sound _ _ [192,33,40,257,96] 13 (by decide) (choices 1) [2,4,16,128] r15878 c15878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5612
  · exact u5613
  · exact u5614
  · exact u5615

def b15879 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 35 44 265 208 54 118 182 310), lower := (rows 193 35 44 265 208 32 64 128 256), losses := [] }

theorem u15879 : Upper (D 8) (R 8) [192,33,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15880 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 266 81 180 244 180 436), lower := (rows 193 35 44 266 81 32 64 128 256), losses := [] }

theorem u15880 : Upper (D 8) (R 8) [192,33,40,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15881 : Route 9 := (fun mask => (mask,id))

def c15881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15881 : Upper (D 8) (R 8) [192,33,40,258,68] 13 := by
  apply FastRouting.sound _ _ [192,33,40,258,68] 13 (by decide) (choices 1) [1,16,128] r15881 c15881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5616
  · exact u5617
  · exact u5618

def r15882 : Route 9 := (fun mask => (mask,id))

def c15882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15882 : Upper (D 8) (R 8) [192,33,40,258,96] 13 := by
  apply FastRouting.sound _ _ [192,33,40,258,96] 13 (by decide) (choices 1) [1,4,16,128] r15882 c15882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5619
  · exact u5620
  · exact u5621
  · exact u5622

def b15883 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 35 44 266 208 53 117 181 309), lower := (rows 193 35 44 266 208 32 64 128 256), losses := [] }

theorem u15883 : Upper (D 8) (R 8) [192,33,40,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15884 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 268 81 178 242 178 434), lower := (rows 193 35 44 268 81 32 64 128 256), losses := [] }

theorem u15884 : Upper (D 8) (R 8) [192,33,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15885 : Route 9 := (fun mask => (mask,id))

def c15885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15885 : Upper (D 8) (R 8) [192,33,40,260,66] 13 := by
  apply FastRouting.sound _ _ [192,33,40,260,66] 13 (by decide) (choices 1) [1,16,128] r15885 c15885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5623
  · exact u5624
  · exact u5625

def r15886 : Route 9 := (fun mask => (mask,id))

def c15886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15886 : Upper (D 8) (R 8) [192,33,40,260,96] 13 := by
  apply FastRouting.sound _ _ [192,33,40,260,96] 13 (by decide) (choices 1) [1,2,16,128] r15886 c15886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5626
  · exact u5627
  · exact u5628
  · exact u5629

def b15887 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 35 44 268 208 51 115 179 307), lower := (rows 193 35 44 268 208 32 64 128 256), losses := [] }

theorem u15887 : Upper (D 8) (R 8) [192,33,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15888 : PairBound 9 := { available := 166, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 280 81 166 230 166 422), lower := (rows 193 35 44 280 81 32 64 128 256), losses := [] }

theorem u15888 : Upper (D 8) (R 8) [192,33,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15889 : Route 9 := (fun mask => (mask,id))

def c15889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15889 : Upper (D 8) (R 8) [192,33,40,272,66] 13 := by
  apply FastRouting.sound _ _ [192,33,40,272,66] 13 (by decide) (choices 1) [1,4,128] r15889 c15889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5630
  · exact u5631
  · exact u5632

def b15890 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 280 84 163 227 163 419), lower := (rows 193 35 44 280 84 32 64 128 256), losses := [] }

theorem u15890 : Upper (D 8) (R 8) [192,33,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15891 : Route 9 := (fun mask => (mask,id))

def c15891 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15891 : Upper (D 8) (R 8) [192,33,40,272,96] 13 := by
  apply FastRouting.sound _ _ [192,33,40,272,96] 13 (by decide) (choices 1) [1,2,4,128] r15891 c15891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5633
  · exact u5634
  · exact u5635
  · exact u5636

def b15892 : PairBound 9 := { available := 39, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 35 44 280 208 39 103 167 295), lower := (rows 193 35 44 280 208 32 64 128 256), losses := [] }

theorem u15892 : Upper (D 8) (R 8) [192,33,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15893 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 296 82 181 213 149 405), lower := (rows 193 35 44 296 82 32 64 128 256), losses := [] }

theorem u15893 : Upper (D 8) (R 8) [192,33,40,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15894 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 296 84 179 211 147 403), lower := (rows 193 35 44 296 84 32 64 128 256), losses := [] }

theorem u15894 : Upper (D 8) (R 8) [192,33,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15895 : PairBound 9 := { available := 54, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 328 145 54 118 182 310), lower := (rows 193 35 44 328 145 32 64 128 256), losses := [] }

theorem u15895 : Upper (D 8) (R 8) [192,33,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15896 : Route 9 := (fun mask => (mask,id))

def c15896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15896 : Upper (D 8) (R 8) [192,33,40,320,130] 13 := by
  apply FastRouting.sound _ _ [192,33,40,320,130] 13 (by decide) (choices 1) [1,4,16] r15896 c15896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5637
  · exact u5638
  · exact u5639

def r15897 : Route 9 := (fun mask => (mask,id))

def c15897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15897 : Upper (D 8) (R 8) [192,33,40,320,132] 13 := by
  apply FastRouting.sound _ _ [192,33,40,320,132] 13 (by decide) (choices 1) [1,2,16] r15897 c15897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5640
  · exact u5641
  · exact u5642

def r15898 : Route 9 := (fun mask => (mask,id))

def c15898 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15898 : Upper (D 8) (R 8) [192,33,40,320,160] 13 := by
  apply FastRouting.sound _ _ [192,33,40,320,160] 13 (by decide) (choices 1) [1,2,4,16] r15898 c15898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5643
  · exact u5644
  · exact u5645
  · exact u5646

def b15899 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 138 276 56 120 184 312), lower := (rows 193 35 69 138 276 32 64 128 256), losses := [] }

theorem u15899 : Upper (D 8) (R 8) [192,33,65,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15899
end Delivery.IrregularNine14.P08
