import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0065
import IrregularNine14P07C0066

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16860 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 200 146 34 337 401 273), lower := (rows 13 98 37 200 146 34 64 128 256), losses := [] }

theorem u16860 : Upper (D 7) (R 7) [12,96,33,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16861 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 37 200 146 48 323 387 259), lower := (rows 13 98 37 200 146 48 64 128 256), losses := [] }

theorem u16861 : Upper (D 7) (R 7) [12,96,33,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16861 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16862 : Route 9 := (fun mask => (mask,id))

def c16862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16862 : Upper (D 7) (R 7) [12,96,33,192,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,130,256] 13 (by decide) (choices 1) [1,2,16] r16862 c16862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3941
  · exact u3942
  · exact u3943

def b16863 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 200 273 34 210 146 402), lower := (rows 13 98 37 200 273 34 64 128 256), losses := [] }

theorem u16863 : Upper (D 7) (R 7) [12,96,33,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16864 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 98 37 200 273 48 194 130 386), lower := (rows 13 98 37 200 273 48 64 128 256), losses := [] }

theorem u16864 : Upper (D 7) (R 7) [12,96,33,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16864 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16865 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 200 273 160 82 146 274), lower := (rows 13 98 37 200 273 160 64 128 256), losses := [] }

theorem u16865 : Upper (D 7) (R 7) [12,96,33,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16866 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 200 274 33 210 146 402), lower := (rows 13 98 37 200 274 33 64 128 256), losses := [] }

theorem u16866 : Upper (D 7) (R 7) [12,96,33,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16867 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 200 274 34 209 145 401), lower := (rows 13 98 37 200 274 34 64 128 256), losses := [] }

theorem u16867 : Upper (D 7) (R 7) [12,96,33,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16868 : Route 9 := (fun mask => (mask,id))

def c16868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16868 : Upper (D 7) (R 7) [12,96,33,192,258,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,258,16] 13 (by decide) (choices 1) [1,2,128] r16868 c16868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3944
  · exact u3945
  · exact u3946

def b16869 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 200 274 160 83 147 275), lower := (rows 13 98 37 200 274 160 64 128 256), losses := [] }

theorem u16869 : Upper (D 7) (R 7) [12,96,33,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16870 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 200 400 33 82 146 274), lower := (rows 13 98 37 200 400 33 64 128 256), losses := [] }

theorem u16870 : Upper (D 7) (R 7) [12,96,33,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16871 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 200 400 34 83 147 275), lower := (rows 13 98 37 200 400 34 64 128 256), losses := [] }

theorem u16871 : Upper (D 7) (R 7) [12,96,33,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16872 : Route 9 := (fun mask => (mask,id))

def c16872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16872 : Upper (D 7) (R 7) [12,96,33,192,384,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,384,16] 13 (by decide) (choices 1) [1,2] r16872 c16872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3947
  · exact u3948

def b16873 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 265 146 34 208 208 464), lower := (rows 13 98 37 265 146 34 64 128 256), losses := [] }

theorem u16873 : Upper (D 7) (R 7) [12,96,33,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16874 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 98 37 265 146 48 194 194 450), lower := (rows 13 98 37 265 146 48 64 128 256), losses := [] }

theorem u16874 : Upper (D 7) (R 7) [12,96,33,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16875 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 265 146 96 210 146 402), lower := (rows 13 98 37 265 146 96 64 128 256), losses := [] }

theorem u16875 : Upper (D 7) (R 7) [12,96,33,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16876 : Route 9 := (fun mask => (mask,id))

def c16876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16876 : Upper (D 7) (R 7) [12,96,33,257,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,257,130,128] 13 (by decide) (choices 1) [2,16] r16876 c16876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3949
  · exact u3950

def b16877 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 265 208 34 210 146 402), lower := (rows 13 98 37 265 208 34 64 128 256), losses := [] }

theorem u16877 : Upper (D 7) (R 7) [12,96,33,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16878 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 265 208 48 194 130 386), lower := (rows 13 98 37 265 208 48 64 128 256), losses := [] }

theorem u16878 : Upper (D 7) (R 7) [12,96,33,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16878 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16879 : Route 9 := (fun mask => (mask,id))

def c16879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16879 : Upper (D 7) (R 7) [12,96,33,257,192,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,257,192,128] 13 (by decide) (choices 1) [2,16] r16879 c16879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3951
  · exact u3952

def b16880 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 266 81 34 208 144 400), lower := (rows 13 98 37 266 81 34 64 128 256), losses := [] }

theorem u16880 : Upper (D 7) (R 7) [12,96,33,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16881 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 266 81 48 194 130 386), lower := (rows 13 98 37 266 81 48 64 128 256), losses := [] }

theorem u16881 : Upper (D 7) (R 7) [12,96,33,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16881 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16882 : Route 9 := (fun mask => (mask,id))

def c16882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16882 : Upper (D 7) (R 7) [12,96,33,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,65,128] 13 (by decide) (choices 1) [2,16,128] r16882 c16882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3953
  · exact u3954
  · exact u3955

def b16883 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 266 145 34 208 208 464), lower := (rows 13 98 37 266 145 34 64 128 256), losses := [] }

theorem u16883 : Upper (D 7) (R 7) [12,96,33,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16884 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 98 37 266 145 48 194 194 450), lower := (rows 13 98 37 266 145 48 64 128 256), losses := [] }

theorem u16884 : Upper (D 7) (R 7) [12,96,33,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16884 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16885 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 266 145 96 210 146 402), lower := (rows 13 98 37 266 145 96 64 128 256), losses := [] }

theorem u16885 : Upper (D 7) (R 7) [12,96,33,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16886 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 98 37 266 145 160 82 210 338), lower := (rows 13 98 37 266 145 160 64 128 256), losses := [] }

theorem u16886 : Upper (D 7) (R 7) [12,96,33,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16887 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 266 146 33 208 208 464), lower := (rows 13 98 37 266 146 33 64 128 256), losses := [] }

theorem u16887 : Upper (D 7) (R 7) [12,96,33,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16888 : Route 9 := (fun mask => (mask,id))

def c16888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16888 : Upper (D 7) (R 7) [12,96,33,258,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,130,16] 13 (by decide) (choices 1) [1,128] r16888 c16888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3956
  · exact u3957

def b16889 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 266 146 96 209 145 401), lower := (rows 13 98 37 266 146 96 64 128 256), losses := [] }

theorem u16889 : Upper (D 7) (R 7) [12,96,33,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16890 : Route 9 := (fun mask => (mask,id))

def c16890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16890 : Upper (D 7) (R 7) [12,96,33,258,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,130,128] 13 (by decide) (choices 1) [1,16] r16890 c16890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3958
  · exact u3959

def b16891 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 266 208 33 210 146 402), lower := (rows 13 98 37 266 208 33 64 128 256), losses := [] }

theorem u16891 : Upper (D 7) (R 7) [12,96,33,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16892 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 266 208 34 209 145 401), lower := (rows 13 98 37 266 208 34 64 128 256), losses := [] }

theorem u16892 : Upper (D 7) (R 7) [12,96,33,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16893 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 266 208 48 195 131 387), lower := (rows 13 98 37 266 208 48 64 128 256), losses := [] }

theorem u16893 : Upper (D 7) (R 7) [12,96,33,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16893 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16894 : Route 9 := (fun mask => (mask,id))

def c16894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16894 : Upper (D 7) (R 7) [12,96,33,258,192,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,192,128] 13 (by decide) (choices 1) [1,2,16] r16894 c16894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3960
  · exact u3961
  · exact u3962

def b16895 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 98 37 280 19 34 192 192 448), lower := (rows 13 98 37 280 19 34 64 128 256), losses := [] }

theorem u16895 : Upper (D 7) (R 7) [12,96,33,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16896 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 280 19 96 194 130 386), lower := (rows 13 98 37 280 19 96 64 128 256), losses := [] }

theorem u16896 : Upper (D 7) (R 7) [12,96,33,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16897 : Route 9 := (fun mask => (mask,id))

def c16897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16897 : Upper (D 7) (R 7) [12,96,33,272,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,3,128] 13 (by decide) (choices 1) [2,128] r16897 c16897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3963
  · exact u3964

def b16898 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 280 81 34 194 130 386), lower := (rows 13 98 37 280 81 34 64 128 256), losses := [] }

theorem u16898 : Upper (D 7) (R 7) [12,96,33,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16899 : Route 9 := (fun mask => (mask,id))

def c16899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16899 : Upper (D 7) (R 7) [12,96,33,272,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,65,128] 13 (by decide) (choices 1) [2,128] r16899 c16899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3965
  · exact u3966

def b16900 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(3,0)], upper := (rows 13 98 37 280 145 34 194 194 450), lower := (rows 13 98 37 280 145 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 20 0 98 162 290), good := (rows 29 450 477 280 145 450 64 128 256) }] }

theorem u16900 : Upper (D 7) (R 7) [12,96,33,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16901 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 280 145 96 194 130 386), lower := (rows 13 98 37 280 145 96 64 128 256), losses := [] }

theorem u16901 : Upper (D 7) (R 7) [12,96,33,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16902 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 98 37 280 145 160 66 194 322), lower := (rows 13 98 37 280 145 160 64 128 256), losses := [] }

theorem u16902 : Upper (D 7) (R 7) [12,96,33,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16903 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 280 146 33 194 194 450), lower := (rows 13 98 37 280 146 33 64 128 256), losses := [] }

theorem u16903 : Upper (D 7) (R 7) [12,96,33,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16904 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 13 98 37 280 146 34 193 193 449), lower := (rows 13 98 37 280 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 13 34 37 317 178 34 0 128 256) }] }

theorem u16904 : Upper (D 7) (R 7) [12,96,33,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16905 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 280 146 96 195 131 387), lower := (rows 13 98 37 280 146 96 64 128 256), losses := [] }

theorem u16905 : Upper (D 7) (R 7) [12,96,33,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16906 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 66, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 13 98 37 280 146 160 67 195 323), lower := (rows 13 98 37 280 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 96 37 317 176 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 13 34 37 317 178 160 0 160 256) }] }

theorem u16906 : Upper (D 7) (R 7) [12,96,33,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16907 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 280 208 33 194 130 386), lower := (rows 13 98 37 280 208 33 64 128 256), losses := [] }

theorem u16907 : Upper (D 7) (R 7) [12,96,33,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16908 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 280 208 34 195 131 387), lower := (rows 13 98 37 280 208 34 64 128 256), losses := [{ target := 7, region := (rows 9 82 13 8 16 122 64 0 256), good := (rows 45 98 37 319 114 34 98 0 256) }] }

theorem u16908 : Upper (D 7) (R 7) [12,96,33,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16909 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 37 280 208 160 67 131 259), lower := (rows 13 98 37 280 208 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 96 37 317 240 160 64 160 256) }] }

theorem u16909 : Upper (D 7) (R 7) [12,96,33,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16910 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 328 145 34 210 146 402), lower := (rows 13 98 37 328 145 34 64 128 256), losses := [] }

theorem u16910 : Upper (D 7) (R 7) [12,96,33,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16911 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 98 37 328 145 48 194 130 386), lower := (rows 13 98 37 328 145 48 64 128 256), losses := [] }

theorem u16911 : Upper (D 7) (R 7) [12,96,33,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16911 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16912 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 98 37 328 145 160 82 146 274), lower := (rows 13 98 37 328 145 160 64 128 256), losses := [] }

theorem u16912 : Upper (D 7) (R 7) [12,96,33,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16913 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 328 146 33 210 146 402), lower := (rows 13 98 37 328 146 33 64 128 256), losses := [] }

theorem u16913 : Upper (D 7) (R 7) [12,96,33,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16914 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 328 146 34 209 145 401), lower := (rows 13 98 37 328 146 34 64 128 256), losses := [] }

theorem u16914 : Upper (D 7) (R 7) [12,96,33,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16915 : Route 9 := (fun mask => (mask,id))

def c16915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16915 : Upper (D 7) (R 7) [12,96,33,320,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320,130,16] 13 (by decide) (choices 1) [1,2,128] r16915 c16915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3967
  · exact u3968
  · exact u3969

def r16916 : Route 9 := (fun mask => (mask,id))

def c16916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16916 : Upper (D 7) (R 7) [12,96,33,320,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320,130,128] 13 (by decide) (choices 1) [1,2,16] r16916 c16916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3970
  · exact u3971
  · exact u3972

def b16917 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 98 37 392 19 34 208 208 464), lower := (rows 13 98 37 392 19 34 64 128 256), losses := [] }

theorem u16917 : Upper (D 7) (R 7) [12,96,33,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16918 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 98 37 392 19 48 194 194 450), lower := (rows 13 98 37 392 19 48 64 128 256), losses := [] }

theorem u16918 : Upper (D 7) (R 7) [12,96,33,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16919 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 392 19 96 210 146 402), lower := (rows 13 98 37 392 19 96 64 128 256), losses := [] }

theorem u16919 : Upper (D 7) (R 7) [12,96,33,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16919
end Delivery.IrregularNine14.P07
