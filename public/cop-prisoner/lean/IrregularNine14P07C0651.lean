import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0446
import IrregularNine14P07C0447

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39060 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 13 74 19 240 208 208 464), lower := (rows 37 290 13 74 19 32 64 128 256), losses := [] }

theorem u39060 : Upper (D 7) (R 7) [36,288,9,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39061 : Route 9 := (fun mask => (mask,id))

def c39061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39061 : Upper (D 7) (R 7) [36,288,9,66,65] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,65] 13 (by decide) (choices 1) [2,16,128] r39061 c39061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26764
  · exact u26765
  · exact u26766

def b39062 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 37 290 13 74 82 177 209 145 401), lower := (rows 37 290 13 74 82 32 64 128 256), losses := [] }

theorem u39062 : Upper (D 7) (R 7) [36,288,9,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39063 : Route 9 := (fun mask => (mask,id))

def c39063 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39063 : Upper (D 7) (R 7) [36,288,9,66,129] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,129] 13 (by decide) (choices 1) [2,16,64,128] r39063 c39063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26767
  · exact u26768
  · exact u26769
  · exact u26770

def r39064 : Route 9 := (fun mask => (mask,id))

def c39064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39064 : Upper (D 7) (R 7) [36,288,9,66,130] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,130] 13 (by decide) (choices 1) [1,16,64,128] r39064 c39064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26771
  · exact u26772
  · exact u26773
  · exact u26774

def r39065 : Route 9 := (fun mask => (mask,id))

def c39065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39065 : Upper (D 7) (R 7) [36,288,9,66,192] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,192] 13 (by decide) (choices 1) [1,2,16,128] r39065 c39065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26775
  · exact u26776
  · exact u26777
  · exact u26778

def b39066 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 13 88 19 226 194 194 450), lower := (rows 37 290 13 88 19 32 64 128 256), losses := [] }

theorem u39066 : Upper (D 7) (R 7) [36,288,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39067 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 37 290 13 88 81 162 194 130 386), lower := (rows 37 290 13 88 81 32 64 128 256), losses := [] }

theorem u39067 : Upper (D 7) (R 7) [36,288,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39068 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 13 88 82 163 195 131 387), lower := (rows 37 290 13 88 82 32 64 128 256), losses := [] }

theorem u39068 : Upper (D 7) (R 7) [36,288,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39069 : Route 9 := (fun mask => (mask,id))

def c39069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39069 : Upper (D 7) (R 7) [36,288,9,80,129] 13 := by
  apply FastRouting.sound _ _ [36,288,9,80,129] 13 (by decide) (choices 1) [2,64,128] r39069 c39069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26779
  · exact u26780
  · exact u26781

def r39070 : Route 9 := (fun mask => (mask,id))

def c39070 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39070 : Upper (D 7) (R 7) [36,288,9,80,130] 13 := by
  apply FastRouting.sound _ _ [36,288,9,80,130] 13 (by decide) (choices 1) [1,2,64,128] r39070 c39070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26782
  · exact u26783
  · exact u26784
  · exact u26785

def b39071 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 13 88 208 163 195 131 387), lower := (rows 37 290 13 88 208 32 64 128 256), losses := [] }

theorem u39071 : Upper (D 7) (R 7) [36,288,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39072 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 13 200 19 242 210 210 466), lower := (rows 37 290 13 200 19 32 64 128 256), losses := [] }

theorem u39072 : Upper (D 7) (R 7) [36,288,9,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39073 : Route 9 := (fun mask => (mask,id))

def c39073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39073 : Upper (D 7) (R 7) [36,288,9,192,65] 13 := by
  apply FastRouting.sound _ _ [36,288,9,192,65] 13 (by decide) (choices 1) [2,16,128] r39073 c39073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26786
  · exact u26787
  · exact u26788

def r39074 : Route 9 := (fun mask => (mask,id))

def c39074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39074 : Upper (D 7) (R 7) [36,288,9,192,66] 13 := by
  apply FastRouting.sound _ _ [36,288,9,192,66] 13 (by decide) (choices 1) [1,2,16,128] r39074 c39074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26789
  · exact u26790
  · exact u26791
  · exact u26792

def b39075 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 290 13 200 208 51 83 147 275), lower := (rows 37 290 13 200 208 32 64 128 256), losses := [] }

theorem u39075 : Upper (D 7) (R 7) [36,288,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39076 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 14 25 19 224 192 192 448), lower := (rows 37 290 14 25 19 32 64 128 256), losses := [] }

theorem u39076 : Upper (D 7) (R 7) [36,288,10,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39077 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 290 14 25 81 226 194 194 450), lower := (rows 37 290 14 25 81 32 64 128 256), losses := [] }

theorem u39077 : Upper (D 7) (R 7) [36,288,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39078 : Route 9 := (fun mask => (mask,id))

def c39078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39078 : Upper (D 7) (R 7) [36,288,10,17,66] 13 := by
  apply FastRouting.sound _ _ [36,288,10,17,66] 13 (by decide) (choices 1) [1,64,128] r39078 c39078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26793
  · exact u26794
  · exact u26795

def r39079 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39079 : Upper (D 7) (R 7) [36,288,10,17,192] 13 := by
  apply FastRouting.sound _ _ [36,288,10,17,192] 13 (by decide) (choices 1) [1,2,64] r39079 c39079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26796
  · exact u26797
  · exact u26798

def b39080 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 200, targets := 2 }], pairs := [(1,0),(2,5),(3,1),(3,5)], upper := (rows 37 290 14 73 19 240 208 208 464), lower := (rows 37 290 14 73 19 32 64 128 256), losses := [] }

theorem u39080 : Upper (D 7) (R 7) [36,288,10,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39081 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 37 290 14 73 81 178 210 146 402), lower := (rows 37 290 14 73 81 32 64 128 256), losses := [] }

theorem u39081 : Upper (D 7) (R 7) [36,288,10,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39082 : Route 9 := (fun mask => (mask,id))

def c39082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39082 : Upper (D 7) (R 7) [36,288,10,65,66] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,66] 13 (by decide) (choices 1) [1,16,128] r39082 c39082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26799
  · exact u26800
  · exact u26801

def r39083 : Route 9 := (fun mask => (mask,id))

def c39083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39083 : Upper (D 7) (R 7) [36,288,10,65,129] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,129] 13 (by decide) (choices 1) [2,16,64,128] r39083 c39083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26802
  · exact u26803
  · exact u26804
  · exact u26805

def r39084 : Route 9 := (fun mask => (mask,id))

def c39084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39084 : Upper (D 7) (R 7) [36,288,10,65,130] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,130] 13 (by decide) (choices 1) [1,16,64,128] r39084 c39084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26806
  · exact u26807
  · exact u26808
  · exact u26809

def r39085 : Route 9 := (fun mask => (mask,id))

def c39085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39085 : Upper (D 7) (R 7) [36,288,10,65,192] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,192] 13 (by decide) (choices 1) [1,2,16,128] r39085 c39085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26810
  · exact u26811
  · exact u26812
  · exact u26813

def b39086 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 200, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(3,5)], upper := (rows 37 290 14 88 19 225 193 193 449), lower := (rows 37 290 14 88 19 32 64 128 256), losses := [] }

theorem u39086 : Upper (D 7) (R 7) [36,288,10,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39087 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 14 88 81 163 195 131 387), lower := (rows 37 290 14 88 81 32 64 128 256), losses := [] }

theorem u39087 : Upper (D 7) (R 7) [36,288,10,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39088 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 290 14 88 82 161 193 129 385), lower := (rows 37 290 14 88 82 32 64 128 256), losses := [] }

theorem u39088 : Upper (D 7) (R 7) [36,288,10,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39089 : Route 9 := (fun mask => (mask,id))

def c39089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39089 : Upper (D 7) (R 7) [36,288,10,80,129] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80,129] 13 (by decide) (choices 1) [1,2,64,128] r39089 c39089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26814
  · exact u26815
  · exact u26816
  · exact u26817

def r39090 : Route 9 := (fun mask => (mask,id))

def c39090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39090 : Upper (D 7) (R 7) [36,288,10,80,130] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80,130] 13 (by decide) (choices 1) [1,64,128] r39090 c39090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26818
  · exact u26819
  · exact u26820

def b39091 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 14 88 208 163 195 131 387), lower := (rows 37 290 14 88 208 32 64 128 256), losses := [] }

theorem u39091 : Upper (D 7) (R 7) [36,288,10,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39092 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39092 : Upper (D 7) (R 7) [36,288,10,192,3] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192,3] 13 (by decide) (choices 1) [1,16,64] r39092 c39092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26821
  · exact u26822
  · exact u26823

def r39093 : Route 9 := (fun mask => (mask,id))

def c39093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39093 : Upper (D 7) (R 7) [36,288,10,192,65] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192,65] 13 (by decide) (choices 1) [1,2,16,128] r39093 c39093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26824
  · exact u26825
  · exact u26826
  · exact u26827

def r39094 : Route 9 := (fun mask => (mask,id))

def c39094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39094 : Upper (D 7) (R 7) [36,288,10,192,66] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192,66] 13 (by decide) (choices 1) [1,16,128] r39094 c39094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26828
  · exact u26829
  · exact u26830

def b39095 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 290 14 200 208 51 83 147 275), lower := (rows 37 290 14 200 208 32 64 128 256), losses := [] }

theorem u39095 : Upper (D 7) (R 7) [36,288,10,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39096 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 28 11 19 224 192 192 448), lower := (rows 37 290 28 11 19 32 64 128 256), losses := [] }

theorem u39096 : Upper (D 7) (R 7) [36,288,24,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39097 : Route 9 := (fun mask => (mask,id))

def c39097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39097 : Upper (D 7) (R 7) [36,288,24,3,65] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3,65] 13 (by decide) (choices 1) [2,64,128] r39097 c39097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26831
  · exact u26832
  · exact u26833

def r39098 : Route 9 := (fun mask => (mask,id))

def c39098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39098 : Upper (D 7) (R 7) [36,288,24,3,66] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3,66] 13 (by decide) (choices 1) [1,64,128] r39098 c39098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26834
  · exact u26835
  · exact u26836

def r39099 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39099 : Upper (D 7) (R 7) [36,288,24,3,192] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3,192] 13 (by decide) (choices 1) [1,2,64] r39099 c39099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26837
  · exact u26838
  · exact u26839

def b39100 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 20, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(4,1)], upper := (rows 37 290 28 73 81 162 194 130 386), lower := (rows 37 290 28 73 81 32 64 128 256), losses := [] }

theorem u39100 : Upper (D 7) (R 7) [36,288,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39101 : Route 9 := (fun mask => (mask,id))

def c39101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39101 : Upper (D 7) (R 7) [36,288,24,65,66] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65,66] 13 (by decide) (choices 1) [1,2,128] r39101 c39101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26840
  · exact u26841
  · exact u26842

theorem m39102_128 : Upper (D 7) (R 7) [36,288,24,65,129,128] 13 :=
  permutation_upper _ _ _ [36,288,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26844

def r39102 : Route 9 := (fun mask => (mask,id))

def c39102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39102 : Upper (D 7) (R 7) [36,288,24,65,129] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65,129] 13 (by decide) (choices 1) [2,64,128] r39102 c39102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26843
  · exact u26844
  · exact m39102_128

def r39103 : Route 9 := (fun mask => (mask,id))

def c39103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39103 : Upper (D 7) (R 7) [36,288,24,65,130] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65,130] 13 (by decide) (choices 1) [1,2,64,128] r39103 c39103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26845
  · exact u26846
  · exact u26847
  · exact u26848

def r39104 : Route 9 := (fun mask => (mask,id))

def c39104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39104 : Upper (D 7) (R 7) [36,288,24,65,192] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65,192] 13 (by decide) (choices 1) [1,2,128] r39104 c39104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26849
  · exact u26850
  · exact u26851

def b39105 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 290 28 74 82 161 193 129 385), lower := (rows 37 290 28 74 82 32 64 128 256), losses := [] }

theorem u39105 : Upper (D 7) (R 7) [36,288,24,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m39106_128 : Upper (D 7) (R 7) [36,288,24,66,130,128] 13 :=
  permutation_upper _ _ _ [36,288,24,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26853

def r39106 : Route 9 := (fun mask => (mask,id))

def c39106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39106 : Upper (D 7) (R 7) [36,288,24,66,130] 13 := by
  apply FastRouting.sound _ _ [36,288,24,66,130] 13 (by decide) (choices 1) [1,64,128] r39106 c39106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26852
  · exact u26853
  · exact m39106_128

def r39107 : Route 9 := (fun mask => (mask,id))

def c39107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39107 : Upper (D 7) (R 7) [36,288,24,66,192] 13 := by
  apply FastRouting.sound _ _ [36,288,24,66,192] 13 (by decide) (choices 1) [1,2,128] r39107 c39107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26854
  · exact u26855
  · exact u26856

def b39108 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 37 290 28 200 208 35 67 131 259), lower := (rows 37 290 28 200 208 32 64 128 256), losses := [] }

theorem u39108 : Upper (D 7) (R 7) [36,288,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39109 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 26 240 208 208 464), lower := (rows 37 290 69 11 26 32 64 128 256), losses := [] }

theorem u39109 : Upper (D 7) (R 7) [36,288,65,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39110 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 82 184 216 152 408), lower := (rows 37 290 69 11 82 32 64 128 256), losses := [] }

theorem u39110 : Upper (D 7) (R 7) [36,288,65,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39111 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 88 178 210 146 402), lower := (rows 37 290 69 11 88 32 64 128 256), losses := [] }

theorem u39111 : Upper (D 7) (R 7) [36,288,65,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39112 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 146 248 216 216 472), lower := (rows 37 290 69 11 146 32 64 128 256), losses := [] }

theorem u39112 : Upper (D 7) (R 7) [36,288,65,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39113 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 152 242 210 210 466), lower := (rows 37 290 69 11 152 32 64 128 256), losses := [] }

theorem u39113 : Upper (D 7) (R 7) [36,288,65,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39114 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 69 11 208 186 218 154 410), lower := (rows 37 290 69 11 208 32 64 128 256), losses := [] }

theorem u39114 : Upper (D 7) (R 7) [36,288,65,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39115 : Route 9 := (fun mask => (mask,id))

def c39115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39115 : Upper (D 7) (R 7) [36,288,65,17,10] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,10] 13 (by decide) (choices 1) [2,64,128] r39115 c39115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26857
  · exact u26858
  · exact u26859

def r39116 : Route 9 := (fun mask => (mask,id))

def c39116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39116 : Upper (D 7) (R 7) [36,288,65,17,66] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,66] 13 (by decide) (choices 1) [2,8,128] r39116 c39116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26860
  · exact u26861
  · exact u26862

def b39117 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 37 290 69 25 88 162 194 130 386), lower := (rows 37 290 69 25 88 32 64 128 256), losses := [] }

theorem u39117 : Upper (D 7) (R 7) [36,288,65,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39118 : Route 9 := (fun mask => (mask,id))

def c39118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39118 : Upper (D 7) (R 7) [36,288,65,17,130] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,130] 13 (by decide) (choices 1) [2,8,64,128] r39118 c39118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26863
  · exact u26864
  · exact u26865
  · exact u26866

def r39119 : Route 9 := (fun mask => (mask,id))

def c39119 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39119 : Upper (D 7) (R 7) [36,288,65,17,136] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,136] 13 (by decide) (choices 1) [2,64,128] r39119 c39119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26867
  · exact u26868
  · exact u26869

#print axioms u39119
end Delivery.IrregularNine14.P07
