import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0101
import IrregularNine14P08C0102
import IrregularNine14P08C0103

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16860 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 137 208 37 101 165 293), lower := (rows 259 98 28 137 208 32 64 128 256), losses := [] }

theorem u16860 : Upper (D 8) (R 8) [258,96,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16861 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 140 176 97 97 225 353), lower := (rows 259 98 28 140 176 32 64 128 256), losses := [] }

theorem u16861 : Upper (D 8) (R 8) [258,96,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16862 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 140 208 33 97 161 289), lower := (rows 259 98 28 140 208 32 64 128 256), losses := [] }

theorem u16862 : Upper (D 8) (R 8) [258,96,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16863 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 168 176 101 69 197 325), lower := (rows 259 98 28 168 176 32 64 128 256), losses := [] }

theorem u16863 : Upper (D 8) (R 8) [258,96,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16864 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 168 208 37 101 165 293), lower := (rows 259 98 28 168 208 32 64 128 256), losses := [] }

theorem u16864 : Upper (D 8) (R 8) [258,96,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16865 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 37 41 84 184 216 152 408), lower := (rows 259 98 37 41 84 32 64 128 256), losses := [] }

theorem u16865 : Upper (D 8) (R 8) [258,96,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16866 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 37 41 148 248 216 216 472), lower := (rows 259 98 37 41 148 32 64 128 256), losses := [] }

theorem u16866 : Upper (D 8) (R 8) [258,96,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16867 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 37 41 208 188 220 156 412), lower := (rows 259 98 37 41 208 32 64 128 256), losses := [] }

theorem u16867 : Upper (D 8) (R 8) [258,96,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16868 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 44 88 177 209 145 401), lower := (rows 259 98 37 44 88 32 64 128 256), losses := [] }

theorem u16868 : Upper (D 8) (R 8) [258,96,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16869 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 44 145 248 216 216 472), lower := (rows 259 98 37 44 145 32 64 128 256), losses := [] }

theorem u16869 : Upper (D 8) (R 8) [258,96,33,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16870 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 44 152 241 209 209 465), lower := (rows 259 98 37 44 152 32 64 128 256), losses := [] }

theorem u16870 : Upper (D 8) (R 8) [258,96,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16871 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 44 208 185 217 153 409), lower := (rows 259 98 37 44 208 32 64 128 256), losses := [] }

theorem u16871 : Upper (D 8) (R 8) [258,96,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16872 : PairBound 9 := { available := 140, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 56 81 172 204 140 396), lower := (rows 259 98 37 56 81 32 64 128 256), losses := [] }

theorem u16872 : Upper (D 8) (R 8) [258,96,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16873 : Route 9 := (fun mask => (mask,id))

def c16873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16873 : Upper (D 8) (R 8) [258,96,33,48,68] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,68] 13 (by decide) (choices 1) [1,8,128] r16873 c16873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6119
  · exact u6120
  · exact u6121

def b16874 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 56 88 165 197 133 389), lower := (rows 259 98 37 56 88 32 64 128 256), losses := [] }

theorem u16874 : Upper (D 8) (R 8) [258,96,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16875 : Route 9 := (fun mask => (mask,id))

def c16875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16875 : Upper (D 8) (R 8) [258,96,33,48,129] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,129] 13 (by decide) (choices 1) [4,8,64,128] r16875 c16875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6122
  · exact u6123
  · exact u6124
  · exact u6125

def r16876 : Route 9 := (fun mask => (mask,id))

def c16876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16876 : Upper (D 8) (R 8) [258,96,33,48,132] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,132] 13 (by decide) (choices 1) [1,8,64,128] r16876 c16876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6126
  · exact u6127
  · exact u6128
  · exact u6129

def r16877 : Route 9 := (fun mask => (mask,id))

def c16877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16877 : Upper (D 8) (R 8) [258,96,33,48,136] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,136] 13 (by decide) (choices 1) [1,4,64,128] r16877 c16877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6130
  · exact u6131
  · exact u6132
  · exact u6133

def r16878 : Route 9 := (fun mask => (mask,id))

def c16878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16878 : Upper (D 8) (R 8) [258,96,33,48,192] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,192] 13 (by decide) (choices 1) [1,4,8,128] r16878 c16878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6134
  · exact u6135
  · exact u6136
  · exact u6137

def b16879 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 73 148 184 248 184 440), lower := (rows 259 98 37 73 148 32 64 128 256), losses := [] }

theorem u16879 : Upper (D 8) (R 8) [258,96,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16880 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 73 152 180 244 180 436), lower := (rows 259 98 37 73 152 32 64 128 256), losses := [] }

theorem u16880 : Upper (D 8) (R 8) [258,96,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16881 : PairBound 9 := { available := 156, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 73 176 188 220 156 412), lower := (rows 259 98 37 73 176 32 64 128 256), losses := [] }

theorem u16881 : Upper (D 8) (R 8) [258,96,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16882 : Route 9 := (fun mask => (mask,id))

def c16882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16882 : Upper (D 8) (R 8) [258,96,33,68,129] 13 := by
  apply FastRouting.sound _ _ [258,96,33,68,129] 13 (by decide) (choices 1) [8,16,128] r16882 c16882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6138
  · exact u6139
  · exact u6140

def r16883 : Route 9 := (fun mask => (mask,id))

def c16883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16883 : Upper (D 8) (R 8) [258,96,33,68,136] 13 := by
  apply FastRouting.sound _ _ [258,96,33,68,136] 13 (by decide) (choices 1) [1,16,128] r16883 c16883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6141
  · exact u6142
  · exact u6143

def r16884 : Route 9 := (fun mask => (mask,id))

def c16884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16884 : Upper (D 8) (R 8) [258,96,33,68,160] 13 := by
  apply FastRouting.sound _ _ [258,96,33,68,160] 13 (by decide) (choices 1) [1,8,16,128] r16884 c16884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6144
  · exact u6145
  · exact u6146
  · exact u6147

def r16885 : Route 9 := (fun mask => (mask,id))

def c16885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16885 : Upper (D 8) (R 8) [258,96,33,80,129] 13 := by
  apply FastRouting.sound _ _ [258,96,33,80,129] 13 (by decide) (choices 1) [4,8,128] r16885 c16885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6148
  · exact u6149
  · exact u6150

def r16886 : Route 9 := (fun mask => (mask,id))

def c16886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16886 : Upper (D 8) (R 8) [258,96,33,80,132] 13 := by
  apply FastRouting.sound _ _ [258,96,33,80,132] 13 (by decide) (choices 1) [1,8,128] r16886 c16886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6151
  · exact u6152
  · exact u6153

def b16887 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 88 152 165 229 165 421), lower := (rows 259 98 37 88 152 32 64 128 256), losses := [] }

theorem u16887 : Upper (D 8) (R 8) [258,96,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16888 : Route 9 := (fun mask => (mask,id))

def c16888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16888 : Upper (D 8) (R 8) [258,96,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,96,33,80,160] 13 (by decide) (choices 1) [1,4,8,128] r16888 c16888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6154
  · exact u6155
  · exact u6156
  · exact u6157

def b16889 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 104 145 188 220 156 412), lower := (rows 259 98 37 104 145 32 64 128 256), losses := [] }

theorem u16889 : Upper (D 8) (R 8) [258,96,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16890 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 104 148 185 217 153 409), lower := (rows 259 98 37 104 148 32 64 128 256), losses := [] }

theorem u16890 : Upper (D 8) (R 8) [258,96,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16891 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 104 152 181 213 149 405), lower := (rows 259 98 37 104 152 32 64 128 256), losses := [] }

theorem u16891 : Upper (D 8) (R 8) [258,96,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16892 : Route 9 := (fun mask => (mask,id))

def c16892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16892 : Upper (D 8) (R 8) [258,96,33,129,132] 13 := by
  apply FastRouting.sound _ _ [258,96,33,129,132] 13 (by decide) (choices 1) [8,16,64] r16892 c16892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6158
  · exact u6159
  · exact u6160

def b16893 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 37 137 152 116 116 244 372), lower := (rows 259 98 37 137 152 32 64 128 256), losses := [] }

theorem u16893 : Upper (D 8) (R 8) [258,96,33,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16894 : Route 9 := (fun mask => (mask,id))

def c16894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16894 : Upper (D 8) (R 8) [258,96,33,129,160] 13 := by
  apply FastRouting.sound _ _ [258,96,33,129,160] 13 (by decide) (choices 1) [4,8,16,64] r16894 c16894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6161
  · exact u6162
  · exact u6163
  · exact u6164

def r16895 : Route 9 := (fun mask => (mask,id))

def c16895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16895 : Upper (D 8) (R 8) [258,96,33,129,192] 13 := by
  apply FastRouting.sound _ _ [258,96,33,129,192] 13 (by decide) (choices 1) [4,8,16] r16895 c16895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6165
  · exact u6166
  · exact u6167

def b16896 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 37 140 152 113 113 241 369), lower := (rows 259 98 37 140 152 32 64 128 256), losses := [] }

theorem u16896 : Upper (D 8) (R 8) [258,96,33,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16897 : Route 9 := (fun mask => (mask,id))

def c16897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16897 : Upper (D 8) (R 8) [258,96,33,132,160] 13 := by
  apply FastRouting.sound _ _ [258,96,33,132,160] 13 (by decide) (choices 1) [1,8,16,64] r16897 c16897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6168
  · exact u6169
  · exact u6170
  · exact u6171

def r16898 : Route 9 := (fun mask => (mask,id))

def c16898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16898 : Upper (D 8) (R 8) [258,96,33,132,192] 13 := by
  apply FastRouting.sound _ _ [258,96,33,132,192] 13 (by decide) (choices 1) [1,8,16] r16898 c16898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6172
  · exact u6173
  · exact u6174

def b16899 : PairBound 9 := { available := 101, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 152 152 101 101 229 357), lower := (rows 259 98 37 152 152 32 64 128 256), losses := [] }

theorem u16899 : Upper (D 8) (R 8) [258,96,33,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16900 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 152 176 109 77 205 333), lower := (rows 259 98 37 152 176 32 64 128 256), losses := [] }

theorem u16900 : Upper (D 8) (R 8) [258,96,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16901 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 152 208 45 109 173 301), lower := (rows 259 98 37 152 208 32 64 128 256), losses := [] }

theorem u16901 : Upper (D 8) (R 8) [258,96,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16902 : Route 9 := (fun mask => (mask,id))

def c16902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16902 : Upper (D 8) (R 8) [258,96,33,160,192] 13 := by
  apply FastRouting.sound _ _ [258,96,33,160,192] 13 (by decide) (choices 1) [1,4,8,16] r16902 c16902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6175
  · exact u6176
  · exact u6177
  · exact u6178

def b16903 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 44 145 241 209 209 465), lower := (rows 259 98 44 44 145 32 64 128 256), losses := [] }

theorem u16903 : Upper (D 8) (R 8) [258,96,40,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16904 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 44 208 177 209 145 401), lower := (rows 259 98 44 44 208 32 64 128 256), losses := [] }

theorem u16904 : Upper (D 8) (R 8) [258,96,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16905 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 28, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 56 84 161 193 129 385), lower := (rows 259 98 44 56 84 32 64 128 256), losses := [] }

theorem u16905 : Upper (D 8) (R 8) [258,96,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16906 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 56 145 229 197 197 453), lower := (rows 259 98 44 56 145 32 64 128 256), losses := [] }

theorem u16906 : Upper (D 8) (R 8) [258,96,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16907 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 56 148 225 193 193 449), lower := (rows 259 98 44 56 148 32 64 128 256), losses := [] }

theorem u16907 : Upper (D 8) (R 8) [258,96,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16908 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 56 208 165 197 133 389), lower := (rows 259 98 44 56 208 32 64 128 256), losses := [] }

theorem u16908 : Upper (D 8) (R 8) [258,96,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16909 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 73 145 180 244 180 436), lower := (rows 259 98 44 73 145 32 64 128 256), losses := [] }

theorem u16909 : Upper (D 8) (R 8) [258,96,40,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16910 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 73 148 177 241 177 433), lower := (rows 259 98 44 73 148 32 64 128 256), losses := [] }

theorem u16910 : Upper (D 8) (R 8) [258,96,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16911 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 73 176 181 213 149 405), lower := (rows 259 98 44 73 176 32 64 128 256), losses := [] }

theorem u16911 : Upper (D 8) (R 8) [258,96,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16912 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 76 145 177 241 177 433), lower := (rows 259 98 44 76 145 32 64 128 256), losses := [] }

theorem u16912 : Upper (D 8) (R 8) [258,96,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16913 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 76 176 177 209 145 401), lower := (rows 259 98 44 76 176 32 64 128 256), losses := [] }

theorem u16913 : Upper (D 8) (R 8) [258,96,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16914 : Route 9 := (fun mask => (mask,id))

def c16914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16914 : Upper (D 8) (R 8) [258,96,40,80,129] 13 := by
  apply FastRouting.sound _ _ [258,96,40,80,129] 13 (by decide) (choices 1) [1,4,128] r16914 c16914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6179
  · exact u6180
  · exact u6181

def b16915 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 44 88 148 161 225 161 417), lower := (rows 259 98 44 88 148 32 64 128 256), losses := [] }

theorem u16915 : Upper (D 8) (R 8) [258,96,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16916 : Route 9 := (fun mask => (mask,id))

def c16916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16916 : Upper (D 8) (R 8) [258,96,40,80,160] 13 := by
  apply FastRouting.sound _ _ [258,96,40,80,160] 13 (by decide) (choices 1) [1,4,128] r16916 c16916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6182
  · exact u6183
  · exact u6184

def b16917 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 104 145 181 213 149 405), lower := (rows 259 98 44 104 145 32 64 128 256), losses := [] }

theorem u16917 : Upper (D 8) (R 8) [258,96,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16918 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 104 148 177 209 145 401), lower := (rows 259 98 44 104 148 32 64 128 256), losses := [] }

theorem u16918 : Upper (D 8) (R 8) [258,96,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16919 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 137 81 180 244 180 436), lower := (rows 259 98 44 137 81 32 64 128 256), losses := [] }

theorem u16919 : Upper (D 8) (R 8) [258,96,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16919
end Delivery.IrregularNine14.P08
