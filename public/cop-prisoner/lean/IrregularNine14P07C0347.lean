import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0098
import IrregularNine14P07C0099

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20820 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 104 208 36 209 145 401), lower := (rows 35 259 14 104 208 36 64 128 256), losses := [] }

theorem u20820 : Upper (D 7) (R 7) [34,257,10,96,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20820 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20821 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 14 104 208 48 197 133 389), lower := (rows 35 259 14 104 208 48 64 128 256), losses := [] }

theorem u20821 : Upper (D 7) (R 7) [34,257,10,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20821 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20822 : Route 9 := (fun mask => (mask,id))

def c20822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20822 : Upper (D 7) (R 7) [34,257,10,96,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,192,128] 13 (by decide) (choices 1) [1,4,16] r20822 c20822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5927
  · exact u5928
  · exact u5929

def b20823 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 259 14 200 52 33 208 208 464), lower := (rows 35 259 14 200 52 33 64 128 256), losses := [] }

theorem u20823 : Upper (D 7) (R 7) [34,257,10,192,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20824 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 259 14 200 52 48 193 193 449), lower := (rows 35 259 14 200 52 48 64 128 256), losses := [] }

theorem u20824 : Upper (D 7) (R 7) [34,257,10,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20824 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20825 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 14 200 52 96 209 145 401), lower := (rows 35 259 14 200 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 258 62 232 52 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 20 104 64 128 256), good := (rows 33 257 60 232 52 96 96 128 256) }] }

theorem u20825 : Upper (D 7) (R 7) [34,257,10,192,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20826 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 200 81 36 240 176 432), lower := (rows 35 259 14 200 81 36 64 128 256), losses := [] }

theorem u20826 : Upper (D 7) (R 7) [34,257,10,192,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20826 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20827 : Route 9 := (fun mask => (mask,id))

def c20827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20827 : Upper (D 7) (R 7) [34,257,10,192,65,16] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,65,16] 13 (by decide) (choices 1) [4,32,128] r20827 c20827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5930
  · exact u5931
  · exact u5932

def r20828 : Route 9 := (fun mask => (mask,id))

def c20828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20828 : Upper (D 7) (R 7) [34,257,10,192,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,65,128] 13 (by decide) (choices 1) [4,16,32] r20828 c20828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5933
  · exact u5934
  · exact u5935

def b20829 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 200 84 33 240 176 432), lower := (rows 35 259 14 200 84 33 64 128 256), losses := [] }

theorem u20829 : Upper (D 7) (R 7) [34,257,10,192,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20830 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 35 259 14 200 84 48 225 161 417), lower := (rows 35 259 14 200 84 48 64 128 256), losses := [] }

theorem u20830 : Upper (D 7) (R 7) [34,257,10,192,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20830 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20831 : Route 9 := (fun mask => (mask,id))

def c20831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20831 : Upper (D 7) (R 7) [34,257,10,192,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,68,128] 13 (by decide) (choices 1) [1,16,32] r20831 c20831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5936
  · exact u5937
  · exact u5938

def b20832 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 200 112 33 212 148 404), lower := (rows 35 259 14 200 112 33 64 128 256), losses := [] }

theorem u20832 : Upper (D 7) (R 7) [34,257,10,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20833 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 200 112 36 209 145 401), lower := (rows 35 259 14 200 112 36 64 128 256), losses := [] }

theorem u20833 : Upper (D 7) (R 7) [34,257,10,192,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20833 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20834 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 14 200 112 48 197 133 389), lower := (rows 35 259 14 200 112 48 64 128 256), losses := [] }

theorem u20834 : Upper (D 7) (R 7) [34,257,10,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20834 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20835 : Route 9 := (fun mask => (mask,id))

def c20835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20835 : Upper (D 7) (R 7) [34,257,10,192,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,96,128] 13 (by decide) (choices 1) [1,4,16] r20835 c20835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5939
  · exact u5940
  · exact u5941

def b20836 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 44 208 33 194 194 450), lower := (rows 35 259 28 44 208 33 64 128 256), losses := [] }

theorem u20836 : Upper (D 7) (R 7) [34,257,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20837 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 44 208 34 193 193 449), lower := (rows 35 259 28 44 208 34 64 128 256), losses := [] }

theorem u20837 : Upper (D 7) (R 7) [34,257,24,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20838 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 44, targets := 131 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 35 259 28 44 208 96 195 131 387), lower := (rows 35 259 28 44 208 96 64 128 256), losses := [] }

theorem u20838 : Upper (D 7) (R 7) [34,257,24,36,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20839 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 28 73 82 36 224 160 416), lower := (rows 35 259 28 73 82 36 64 128 256), losses := [] }

theorem u20839 : Upper (D 7) (R 7) [34,257,24,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20839 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20840 : Route 9 := (fun mask => (mask,id))

def c20840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20840 : Upper (D 7) (R 7) [34,257,24,65,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,66,128] 13 (by decide) (choices 1) [4,32,128] r20840 c20840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5942
  · exact u5943
  · exact u5944

def b20841 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 73 112 34 196 132 388), lower := (rows 35 259 28 73 112 34 64 128 256), losses := [] }

theorem u20841 : Upper (D 7) (R 7) [34,257,24,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20842 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 35 259 28 73 112 36 194 130 386), lower := (rows 35 259 28 73 112 36 64 128 256), losses := [] }

theorem u20842 : Upper (D 7) (R 7) [34,257,24,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20842 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20843 : Route 9 := (fun mask => (mask,id))

def c20843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20843 : Upper (D 7) (R 7) [34,257,24,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,96,128] 13 (by decide) (choices 1) [2,4,128] r20843 c20843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5945
  · exact u5946
  · exact u5947

def b20844 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 35 259 28 73 146 36 224 224 480), lower := (rows 35 259 28 73 146 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 44 109 173 301), good := (rows 498 466 508 508 146 484 64 128 256) }] }

theorem u20844 : Upper (D 7) (R 7) [34,257,24,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20844 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20845 : Route 9 := (fun mask => (mask,id))

def c20845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20845 : Upper (D 7) (R 7) [34,257,24,65,130,64] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,130,64] 13 (by decide) (choices 1) [4,32,128] r20845 c20845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5948
  · exact u5949
  · exact u5950

def r20846 : Route 9 := (fun mask => (mask,id))

def c20846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20846 : Upper (D 7) (R 7) [34,257,24,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,130,128] 13 (by decide) (choices 1) [4,32] r20846 c20846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5951
  · exact u5952

def b20847 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 73 148 34 224 224 480), lower := (rows 35 259 28 73 148 34 64 128 256), losses := [] }

theorem u20847 : Upper (D 7) (R 7) [34,257,24,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20848 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 35 259 28 73 148 96 226 162 418), lower := (rows 35 259 28 73 148 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 107 67 131 259), good := (rows 482 482 60 508 148 96 96 128 256) }] }

theorem u20848 : Upper (D 7) (R 7) [34,257,24,65,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20849 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 259 28 73 148 160 98 226 354), lower := (rows 35 259 28 73 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 187 67 131 259), good := (rows 482 482 60 508 180 160 64 160 256) }] }

theorem u20849 : Upper (D 7) (R 7) [34,257,24,65,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20850 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 73 176 34 196 196 452), lower := (rows 35 259 28 73 176 34 64 128 256), losses := [] }

theorem u20850 : Upper (D 7) (R 7) [34,257,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20851 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 208, targets := 1 }], pairs := [(1,5),(3,5),(4,0)], upper := (rows 35 259 28 73 176 36 194 194 450), lower := (rows 35 259 28 73 176 36 64 128 256), losses := [] }

theorem u20851 : Upper (D 7) (R 7) [34,257,24,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20851 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20852 : Route 9 := (fun mask => (mask,id))

def c20852 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20852 : Upper (D 7) (R 7) [34,257,24,65,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,160,64] 13 (by decide) (choices 1) [2,4,128] r20852 c20852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5953
  · exact u5954
  · exact u5955

def b20853 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 28 73 176 160 70 198 326), lower := (rows 35 259 28 73 176 160 64 128 256), losses := [] }

theorem u20853 : Upper (D 7) (R 7) [34,257,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20854 : PairBound 9 := { available := 164, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 73 208 34 228 164 420), lower := (rows 35 259 28 73 208 34 64 128 256), losses := [] }

theorem u20854 : Upper (D 7) (R 7) [34,257,24,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20855 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 35 259 28 73 208 36 226 162 418), lower := (rows 35 259 28 73 208 36 64 128 256), losses := [] }

theorem u20855 : Upper (D 7) (R 7) [34,257,24,65,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20855 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20856 : Route 9 := (fun mask => (mask,id))

def c20856 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20856 : Upper (D 7) (R 7) [34,257,24,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,192,128] 13 (by decide) (choices 1) [2,4,32] r20856 c20856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5956
  · exact u5957
  · exact u5958

def b20857 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 74 112 33 196 132 388), lower := (rows 35 259 28 74 112 33 64 128 256), losses := [] }

theorem u20857 : Upper (D 7) (R 7) [34,257,24,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20858 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 259 28 74 112 36 193 129 385), lower := (rows 35 259 28 74 112 36 64 128 256), losses := [] }

theorem u20858 : Upper (D 7) (R 7) [34,257,24,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20858 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20859 : Route 9 := (fun mask => (mask,id))

def c20859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20859 : Upper (D 7) (R 7) [34,257,24,66,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,96,128] 13 (by decide) (choices 1) [1,4,128] r20859 c20859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5959
  · exact u5960
  · exact u5961

def b20860 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 74 148 33 224 224 480), lower := (rows 35 259 28 74 148 33 64 128 256), losses := [] }

theorem u20860 : Upper (D 7) (R 7) [34,257,24,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20861 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,1)], upper := (rows 35 259 28 74 148 96 225 161 417), lower := (rows 35 259 28 74 148 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 107 67 131 259), good := (rows 481 481 60 508 148 96 96 128 256) }] }

theorem u20861 : Upper (D 7) (R 7) [34,257,24,66,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20862 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 35 259 28 74 148 160 97 225 353), lower := (rows 35 259 28 74 148 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 187 67 131 259), good := (rows 481 481 60 508 180 160 64 160 256) }] }

theorem u20862 : Upper (D 7) (R 7) [34,257,24,66,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20863 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 74 176 33 196 196 452), lower := (rows 35 259 28 74 176 33 64 128 256), losses := [] }

theorem u20863 : Upper (D 7) (R 7) [34,257,24,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20864 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,5),(3,5),(4,1)], upper := (rows 35 259 28 74 176 36 193 193 449), lower := (rows 35 259 28 74 176 36 64 128 256), losses := [] }

theorem u20864 : Upper (D 7) (R 7) [34,257,24,66,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20864 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20865 : Route 9 := (fun mask => (mask,id))

def c20865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20865 : Upper (D 7) (R 7) [34,257,24,66,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,160,64] 13 (by decide) (choices 1) [1,4,128] r20865 c20865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5962
  · exact u5963
  · exact u5964

def b20866 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 28 74 176 160 69 197 325), lower := (rows 35 259 28 74 176 160 64 128 256), losses := [] }

theorem u20866 : Upper (D 7) (R 7) [34,257,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20867 : PairBound 9 := { available := 164, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 74 208 33 228 164 420), lower := (rows 35 259 28 74 208 33 64 128 256), losses := [] }

theorem u20867 : Upper (D 7) (R 7) [34,257,24,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20868 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 35 259 28 74 208 36 225 161 417), lower := (rows 35 259 28 74 208 36 64 128 256), losses := [] }

theorem u20868 : Upper (D 7) (R 7) [34,257,24,66,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20868 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20869 : Route 9 := (fun mask => (mask,id))

def c20869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20869 : Upper (D 7) (R 7) [34,257,24,66,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,192,128] 13 (by decide) (choices 1) [1,4,32] r20869 c20869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5965
  · exact u5966
  · exact u5967

def b20870 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 76 176 33 194 194 450), lower := (rows 35 259 28 76 176 33 64 128 256), losses := [] }

theorem u20870 : Upper (D 7) (R 7) [34,257,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20871 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 76 176 34 193 193 449), lower := (rows 35 259 28 76 176 34 64 128 256), losses := [] }

theorem u20871 : Upper (D 7) (R 7) [34,257,24,68,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20872 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 403, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,6),(1,5),(1,6),(4,6)], upper := (rows 35 259 28 76 176 96 195 131 387), lower := (rows 35 259 28 76 176 96 64 128 256), losses := [] }

theorem u20872 : Upper (D 7) (R 7) [34,257,24,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20873 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 28 76 176 160 67 195 323), lower := (rows 35 259 28 76 176 160 64 128 256), losses := [] }

theorem u20873 : Upper (D 7) (R 7) [34,257,24,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20874 : PairBound 9 := { available := 134, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 104 208 33 198 134 390), lower := (rows 35 259 28 104 208 33 64 128 256), losses := [] }

theorem u20874 : Upper (D 7) (R 7) [34,257,24,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20875 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 28 104 208 34 197 133 389), lower := (rows 35 259 28 104 208 34 64 128 256), losses := [] }

theorem u20875 : Upper (D 7) (R 7) [34,257,24,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20876 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 44, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 35 259 28 104 208 36 195 131 387), lower := (rows 35 259 28 104 208 36 64 128 256), losses := [] }

theorem u20876 : Upper (D 7) (R 7) [34,257,24,96,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20876 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20877 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 35 259 28 104 208 160 71 135 263), lower := (rows 35 259 28 104 208 160 64 128 256), losses := [] }

theorem u20877 : Upper (D 7) (R 7) [34,257,24,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20878 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 73 82 36 208 144 400), lower := (rows 35 259 44 73 82 36 64 128 256), losses := [] }

theorem u20878 : Upper (D 7) (R 7) [34,257,40,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20878 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20879 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 44 73 82 48 196 132 388), lower := (rows 35 259 44 73 82 48 64 128 256), losses := [] }

theorem u20879 : Upper (D 7) (R 7) [34,257,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20879 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20879
end Delivery.IrregularNine14.P07
