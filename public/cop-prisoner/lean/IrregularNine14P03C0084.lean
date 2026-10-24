import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0032

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5040 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 76 112 177 209 145 401), lower := (rows 259 35 13 76 112 32 64 128 256), losses := [] }

theorem u5040 : Upper (D 3) (R 3) [258,33,9,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5040
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5041 : Route 9 := (fun mask => (mask,id))

def c5041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5041 : Upper (D 3) (R 3) [258,33,9,68,129] 13 := by
  apply FastRouting.sound _ _ [258,33,9,68,129] 13 (by decide) (choices 1) [16,64,128] r5041 c5041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1920
  · exact u1921
  · exact u1922

def r5042 : Route 9 := (fun mask => (mask,id))

def c5042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5042 : Upper (D 3) (R 3) [258,33,9,68,160] 13 := by
  apply FastRouting.sound _ _ [258,33,9,68,160] 13 (by decide) (choices 1) [1,16,64,128] r5042 c5042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925
  · exact u1926

def b5043 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 76 208 177 241 177 433), lower := (rows 259 35 13 76 208 32 64 128 256), losses := [] }

theorem u5043 : Upper (D 3) (R 3) [258,33,9,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5043
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 35 13 88 49 228 196 196 452), lower := (rows 259 35 13 88 49 32 64 128 256), losses := [] }

theorem u5044 : Upper (D 3) (R 3) [258,33,9,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5044
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 13 88 52 225 193 193 449), lower := (rows 259 35 13 88 52 32 64 128 256), losses := [] }

theorem u5045 : Upper (D 3) (R 3) [258,33,9,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 88 81 164 228 164 420), lower := (rows 259 35 13 88 81 32 64 128 256), losses := [] }

theorem u5046 : Upper (D 3) (R 3) [258,33,9,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 84 161 225 161 417), lower := (rows 259 35 13 88 84 32 64 128 256), losses := [] }

theorem u5047 : Upper (D 3) (R 3) [258,33,9,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5047
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 112 165 197 133 389), lower := (rows 259 35 13 88 112 32 64 128 256), losses := [] }

theorem u5048 : Upper (D 3) (R 3) [258,33,9,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5049 : Route 9 := (fun mask => (mask,id))

def c5049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5049 : Upper (D 3) (R 3) [258,33,9,80,129] 13 := by
  apply FastRouting.sound _ _ [258,33,9,80,129] 13 (by decide) (choices 1) [4,64,128] r5049 c5049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1927
  · exact u1928
  · exact u1929

def r5050 : Route 9 := (fun mask => (mask,id))

def c5050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5050 : Upper (D 3) (R 3) [258,33,9,80,132] 13 := by
  apply FastRouting.sound _ _ [258,33,9,80,132] 13 (by decide) (choices 1) [1,64,128] r5050 c5050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1930
  · exact u1931
  · exact u1932

def r5051 : Route 9 := (fun mask => (mask,id))

def c5051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5051 : Upper (D 3) (R 3) [258,33,9,80,160] 13 := by
  apply FastRouting.sound _ _ [258,33,9,80,160] 13 (by decide) (choices 1) [1,4,64,128] r5051 c5051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1933
  · exact u1934
  · exact u1935
  · exact u1936

def b5052 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 208 165 229 165 421), lower := (rows 259 35 13 88 208 32 64 128 256), losses := [] }

theorem u5052 : Upper (D 3) (R 3) [258,33,9,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5053 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 104 81 180 212 148 404), lower := (rows 259 35 13 104 81 32 64 128 256), losses := [] }

theorem u5053 : Upper (D 3) (R 3) [258,33,9,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5054 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 104 84 177 209 145 401), lower := (rows 259 35 13 104 84 32 64 128 256), losses := [] }

theorem u5054 : Upper (D 3) (R 3) [258,33,9,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 104 145 244 212 212 468), lower := (rows 259 35 13 104 145 32 64 128 256), losses := [] }

theorem u5055 : Upper (D 3) (R 3) [258,33,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5056 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 104 148 241 209 209 465), lower := (rows 259 35 13 104 148 32 64 128 256), losses := [] }

theorem u5056 : Upper (D 3) (R 3) [258,33,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5056
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5057 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 104 208 181 213 149 405), lower := (rows 259 35 13 104 208 32 64 128 256), losses := [] }

theorem u5057 : Upper (D 3) (R 3) [258,33,9,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5058 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 35 13 200 49 244 212 212 468), lower := (rows 259 35 13 200 49 32 64 128 256), losses := [] }

theorem u5058 : Upper (D 3) (R 3) [258,33,9,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5058
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5059 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5059 : Upper (D 3) (R 3) [258,33,9,192,36] 13 := by
  apply FastRouting.sound _ _ [258,33,9,192,36] 13 (by decide) (choices 1) [1,16,64] r5059 c5059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1937
  · exact u1938
  · exact u1939

def r5060 : Route 9 := (fun mask => (mask,id))

def c5060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5060 : Upper (D 3) (R 3) [258,33,9,192,65] 13 := by
  apply FastRouting.sound _ _ [258,33,9,192,65] 13 (by decide) (choices 1) [4,16,128] r5060 c5060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1940
  · exact u1941
  · exact u1942

def b5061 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 200 84 177 241 177 433), lower := (rows 259 35 13 200 84 32 64 128 256), losses := [] }

theorem u5061 : Upper (D 3) (R 3) [258,33,9,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5062 : Route 9 := (fun mask => (mask,id))

def c5062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5062 : Upper (D 3) (R 3) [258,33,9,192,96] 13 := by
  apply FastRouting.sound _ _ [258,33,9,192,96] 13 (by decide) (choices 1) [1,4,16,128] r5062 c5062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1943
  · exact u1944
  · exact u1945
  · exact u1946

def b5063 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 13 200 208 53 117 181 309), lower := (rows 259 35 13 200 208 32 64 128 256), losses := [] }

theorem u5063 : Upper (D 3) (R 3) [258,33,9,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5064 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 81 228 196 196 452), lower := (rows 259 35 28 41 81 32 64 128 256), losses := [] }

theorem u5064 : Upper (D 3) (R 3) [258,33,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 84 225 193 193 449), lower := (rows 259 35 28 41 84 32 64 128 256), losses := [] }

theorem u5065 : Upper (D 3) (R 3) [258,33,24,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5066 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 208 229 197 197 453), lower := (rows 259 35 28 41 208 32 64 128 256), losses := [] }

theorem u5066 : Upper (D 3) (R 3) [258,33,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5066
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5067 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 28 44 81 225 193 193 449), lower := (rows 259 35 28 44 81 32 64 128 256), losses := [] }

theorem u5067 : Upper (D 3) (R 3) [258,33,24,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5067
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5068 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 28 44 208 225 193 193 449), lower := (rows 259 35 28 44 208 32 64 128 256), losses := [] }

theorem u5068 : Upper (D 3) (R 3) [258,33,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5068
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 28 73 81 164 228 164 420), lower := (rows 259 35 28 73 81 32 64 128 256), losses := [] }

theorem u5069 : Upper (D 3) (R 3) [258,33,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 73 84 161 225 161 417), lower := (rows 259 35 28 73 84 32 64 128 256), losses := [] }

theorem u5070 : Upper (D 3) (R 3) [258,33,24,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5070
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 112 165 197 133 389), lower := (rows 259 35 28 73 112 32 64 128 256), losses := [] }

theorem u5071 : Upper (D 3) (R 3) [258,33,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5071
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5072_128 : Upper (D 3) (R 3) [258,33,24,65,129,128] 13 :=
  permutation_upper _ _ _ [258,33,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1948

def r5072 : Route 9 := (fun mask => (mask,id))

def c5072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5072 : Upper (D 3) (R 3) [258,33,24,65,129] 13 := by
  apply FastRouting.sound _ _ [258,33,24,65,129] 13 (by decide) (choices 1) [4,64,128] r5072 c5072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1947
  · exact u1948
  · exact m5072_128

def r5073 : Route 9 := (fun mask => (mask,id))

def c5073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5073 : Upper (D 3) (R 3) [258,33,24,65,132] 13 := by
  apply FastRouting.sound _ _ [258,33,24,65,132] 13 (by decide) (choices 1) [1,64,128] r5073 c5073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1949
  · exact u1950
  · exact u1951

def r5074 : Route 9 := (fun mask => (mask,id))

def c5074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5074 : Upper (D 3) (R 3) [258,33,24,65,160] 13 := by
  apply FastRouting.sound _ _ [258,33,24,65,160] 13 (by decide) (choices 1) [1,4,64,128] r5074 c5074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1952
  · exact u1953
  · exact u1954
  · exact u1955

def b5075 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 208 165 229 165 421), lower := (rows 259 35 28 73 208 32 64 128 256), losses := [] }

theorem u5075 : Upper (D 3) (R 3) [258,33,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5075
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5076 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 76 112 161 193 129 385), lower := (rows 259 35 28 76 112 32 64 128 256), losses := [] }

theorem u5076 : Upper (D 3) (R 3) [258,33,24,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5077 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 28 76 176 225 193 193 449), lower := (rows 259 35 28 76 176 32 64 128 256), losses := [] }

theorem u5077 : Upper (D 3) (R 3) [258,33,24,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5078 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 76 208 161 225 161 417), lower := (rows 259 35 28 76 208 32 64 128 256), losses := [] }

theorem u5078 : Upper (D 3) (R 3) [258,33,24,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5079 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 104 208 165 197 133 389), lower := (rows 259 35 28 104 208 32 64 128 256), losses := [] }

theorem u5079 : Upper (D 3) (R 3) [258,33,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5079
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 200 208 37 101 165 293), lower := (rows 259 35 28 200 208 32 64 128 256), losses := [] }

theorem u5080 : Upper (D 3) (R 3) [258,33,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 73 84 184 216 152 408), lower := (rows 259 35 37 73 84 32 64 128 256), losses := [] }

theorem u5081 : Upper (D 3) (R 3) [258,33,33,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5081
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 73 148 248 216 216 472), lower := (rows 259 35 37 73 148 32 64 128 256), losses := [] }

theorem u5082 : Upper (D 3) (R 3) [258,33,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5082
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 73 152 244 212 212 468), lower := (rows 259 35 37 73 152 32 64 128 256), losses := [] }

theorem u5083 : Upper (D 3) (R 3) [258,33,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 73 208 188 220 156 412), lower := (rows 259 35 37 73 208 32 64 128 256), losses := [] }

theorem u5084 : Upper (D 3) (R 3) [258,33,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5084
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 152 241 209 209 465), lower := (rows 259 35 37 76 152 32 64 128 256), losses := [] }

theorem u5085 : Upper (D 3) (R 3) [258,33,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5085
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 208 185 217 153 409), lower := (rows 259 35 37 76 208 32 64 128 256), losses := [] }

theorem u5086 : Upper (D 3) (R 3) [258,33,33,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5086
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5087 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 88 152 229 197 197 453), lower := (rows 259 35 37 88 152 32 64 128 256), losses := [] }

theorem u5087 : Upper (D 3) (R 3) [258,33,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5087
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5088 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 44 73 81 180 212 148 404), lower := (rows 259 35 44 73 81 32 64 128 256), losses := [] }

theorem u5088 : Upper (D 3) (R 3) [258,33,40,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5088
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5089 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 73 84 177 209 145 401), lower := (rows 259 35 44 73 84 32 64 128 256), losses := [] }

theorem u5089 : Upper (D 3) (R 3) [258,33,40,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5089
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5090 : Route 9 := (fun mask => (mask,id))

def c5090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5090 : Upper (D 3) (R 3) [258,33,40,65,129] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65,129] 13 (by decide) (choices 1) [4,16,64,128] r5090 c5090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1956
  · exact u1957
  · exact u1958
  · exact u1959

def r5091 : Route 9 := (fun mask => (mask,id))

def c5091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5091 : Upper (D 3) (R 3) [258,33,40,65,132] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65,132] 13 (by decide) (choices 1) [1,16,64,128] r5091 c5091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1960
  · exact u1961
  · exact u1962
  · exact u1963

def r5092 : Route 9 := (fun mask => (mask,id))

def c5092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5092 : Upper (D 3) (R 3) [258,33,40,65,192] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65,192] 13 (by decide) (choices 1) [1,4,16,128] r5092 c5092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1964
  · exact u1965
  · exact u1966
  · exact u1967

def b5093 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 44 76 81 177 209 145 401), lower := (rows 259 35 44 76 81 32 64 128 256), losses := [] }

theorem u5093 : Upper (D 3) (R 3) [258,33,40,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5093
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 44 76 145 241 209 209 465), lower := (rows 259 35 44 76 145 32 64 128 256), losses := [] }

theorem u5094 : Upper (D 3) (R 3) [258,33,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5094
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 44 76 208 177 209 145 401), lower := (rows 259 35 44 76 208 32 64 128 256), losses := [] }

theorem u5095 : Upper (D 3) (R 3) [258,33,40,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 81 165 197 133 389), lower := (rows 259 35 44 88 81 32 64 128 256), losses := [] }

theorem u5096 : Upper (D 3) (R 3) [258,33,40,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5096
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 84 161 193 129 385), lower := (rows 259 35 44 88 84 32 64 128 256), losses := [] }

theorem u5097 : Upper (D 3) (R 3) [258,33,40,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5098 : Route 9 := (fun mask => (mask,id))

def c5098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5098 : Upper (D 3) (R 3) [258,33,40,80,129] 13 := by
  apply FastRouting.sound _ _ [258,33,40,80,129] 13 (by decide) (choices 1) [1,4,64,128] r5098 c5098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1968
  · exact u1969
  · exact u1970
  · exact u1971

def b5099 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 44 88 148 225 193 193 449), lower := (rows 259 35 44 88 148 32 64 128 256), losses := [] }

theorem u5099 : Upper (D 3) (R 3) [258,33,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5099
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P03
