import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0032
import IrregularNine14P00C0033

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 44 73 212 244 212 212 468), lower := (rows 275 35 44 73 16 32 64 128 256), losses := [] }

theorem u3120 : Upper (D 0) (R 0) [274,33,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3120
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 35 44 76 209 241 209 209 465), lower := (rows 275 35 44 76 16 32 64 128 256), losses := [] }

theorem u3121 : Upper (D 0) (R 0) [274,33,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3121
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3122 : Route 9 := (fun mask => (mask,id))

def c3122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3122 : Upper (D 0) (R 0) [274,33,40,80] 13 := by
  apply FastRouting.sound _ _ [274,33,40,80] 13 (by decide) (choices 1) [1,4,64,128] r3122 c3122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1927
  · exact u1928
  · exact u1929
  · exact u1930

def r3123 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3123 : Upper (D 0) (R 0) [274,33,40,192] 13 := by
  apply FastRouting.sound _ _ [274,33,40,192] 13 (by decide) (choices 1) [1,4,64] r3123 c3123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1931
  · exact u1932
  · exact u1933

def b3124 : PairBound 9 := { available := 204, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 73 220 236 204 204 460), lower := (rows 275 35 52 73 16 32 64 128 256), losses := [] }

theorem u3124 : Upper (D 0) (R 0) [274,33,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3124
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3125 : Route 9 := (fun mask => (mask,id))

def c3125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3125 : Upper (D 0) (R 0) [274,33,48,68] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68] 13 (by decide) (choices 1) [1,8,64,128] r3125 c3125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1934
  · exact u1935
  · exact u1936
  · exact u1937

def r3126 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3126 : Upper (D 0) (R 0) [274,33,48,192] 13 := by
  apply FastRouting.sound _ _ [274,33,48,192] 13 (by decide) (choices 1) [1,4,8,64] r3126 c3126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1938
  · exact u1939
  · exact u1940
  · exact u1941

def b3127 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 35 69 76 184 184 248 184 440), lower := (rows 275 35 69 76 16 32 64 128 256), losses := [] }

theorem u3127 : Upper (D 0) (R 0) [274,33,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3127
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 88 188 172 236 172 428), lower := (rows 275 35 69 88 16 32 64 128 256), losses := [] }

theorem u3128 : Upper (D 0) (R 0) [274,33,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3128
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 104 156 188 220 156 412), lower := (rows 275 35 69 104 16 32 64 128 256), losses := [] }

theorem u3129 : Upper (D 0) (R 0) [274,33,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3129
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 140 248 248 248 248 504), lower := (rows 275 35 69 140 16 32 64 128 256), losses := [] }

theorem u3130 : Upper (D 0) (R 0) [274,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3130
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 152 252 236 236 236 492), lower := (rows 275 35 69 152 16 32 64 128 256), losses := [] }

theorem u3131 : Upper (D 0) (R 0) [274,33,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3131
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 168 220 252 220 220 476), lower := (rows 275 35 69 168 16 32 64 128 256), losses := [] }

theorem u3132 : Upper (D 0) (R 0) [274,33,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3132
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3133 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 200 188 188 252 188 444), lower := (rows 275 35 69 200 16 32 64 128 256), losses := [] }

theorem u3133 : Upper (D 0) (R 0) [274,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3133
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 76 177 177 241 177 433), lower := (rows 275 35 76 76 16 32 64 128 256), losses := [] }

theorem u3134 : Upper (D 0) (R 0) [274,33,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3134
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 88 181 165 229 165 421), lower := (rows 275 35 76 88 16 32 64 128 256), losses := [] }

theorem u3135 : Upper (D 0) (R 0) [274,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3135
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 104 149 181 213 149 405), lower := (rows 275 35 76 104 16 32 64 128 256), losses := [] }

theorem u3136 : Upper (D 0) (R 0) [274,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3136
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3137_128 : Upper (D 0) (R 0) [274,33,72,132,128] 13 :=
  permutation_upper _ _ _ [274,33,72,132,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1944

def r3137 : Route 9 := (fun mask => (mask,id))

def c3137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3137 : Upper (D 0) (R 0) [274,33,72,132] 13 := by
  apply FastRouting.sound _ _ [274,33,72,132] 13 (by decide) (choices 1) [1,32,64,128] r3137 c3137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1942
  · exact u1943
  · exact u1944
  · exact m3137_128

def r3138 : Route 9 := (fun mask => (mask,id))

def c3138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3138 : Upper (D 0) (R 0) [274,33,72,144] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144] 13 (by decide) (choices 1) [1,4,32,64,128] r3138 c3138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1945
  · exact u1946
  · exact u1947
  · exact u1948
  · exact u1949

def r3139 : Route 9 := (fun mask => (mask,id))

def c3139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3139 : Upper (D 0) (R 0) [274,33,72,160] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160] 13 (by decide) (choices 1) [1,4,64,128] r3139 c3139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1950
  · exact u1951
  · exact u1952
  · exact u1953

def b3140 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 200 181 181 245 181 437), lower := (rows 275 35 76 200 16 32 64 128 256), losses := [] }

theorem u3140 : Upper (D 0) (R 0) [274,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3140
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3141 : Route 9 := (fun mask => (mask,id))

def c3141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3141 : Upper (D 0) (R 0) [274,33,80,96] 13 := by
  apply FastRouting.sound _ _ [274,33,80,96] 13 (by decide) (choices 1) [1,4,8,128] r3141 c3141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1954
  · exact u1955
  · exact u1956
  · exact u1957

def r3142 : Route 9 := (fun mask => (mask,id))

def c3142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3142 : Upper (D 0) (R 0) [274,33,80,160] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160] 13 (by decide) (choices 1) [1,4,8,64,128] r3142 c3142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1958
  · exact u1959
  · exact u1960
  · exact u1961
  · exact u1962

def r3143 : Route 9 := (fun mask => (mask,id))

def c3143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3143 : Upper (D 0) (R 0) [274,33,80,192] 13 := by
  apply FastRouting.sound _ _ [274,33,80,192] 13 (by decide) (choices 1) [1,4,8,32,128] r3143 c3143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1963
  · exact u1964
  · exact u1965
  · exact u1966
  · exact u1967

def r3144 : Route 9 := (fun mask => (mask,id))

def c3144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3144 : Upper (D 0) (R 0) [274,33,96,192] 13 := by
  apply FastRouting.sound _ _ [274,33,96,192] 13 (by decide) (choices 1) [1,4,8,128] r3144 c3144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1968
  · exact u1969
  · exact u1970
  · exact u1971

def b3145 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 196 200 61 61 125 189 317), lower := (rows 275 35 196 200 16 32 64 128 256), losses := [] }

theorem u3145 : Upper (D 0) (R 0) [274,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3145
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 25 240 224 224 224 480), lower := (rows 275 38 13 25 16 32 64 128 256), losses := [] }

theorem u3146 : Upper (D 0) (R 0) [274,36,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3146
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 13 41 208 240 208 208 464), lower := (rows 275 38 13 41 16 32 64 128 256), losses := [] }

theorem u3147 : Upper (D 0) (R 0) [274,36,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3147
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 13 56 209 225 193 193 449), lower := (rows 275 38 13 56 16 32 64 128 256), losses := [] }

theorem u3148 : Upper (D 0) (R 0) [274,36,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3148
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 38 13 73 240 240 240 240 496), lower := (rows 275 38 13 73 16 32 64 128 256), losses := [] }

theorem u3149 : Upper (D 0) (R 0) [274,36,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3149
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 13 88 241 225 225 225 481), lower := (rows 275 38 13 88 16 32 64 128 256), losses := [] }

theorem u3150 : Upper (D 0) (R 0) [274,36,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3150
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 13 104 209 241 209 209 465), lower := (rows 275 38 13 104 16 32 64 128 256), losses := [] }

theorem u3151 : Upper (D 0) (R 0) [274,36,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3151
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3152 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3152 : Upper (D 0) (R 0) [274,36,9,192] 13 := by
  apply FastRouting.sound _ _ [274,36,9,192] 13 (by decide) (choices 1) [1,32,64] r3152 c3152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1972
  · exact u1973
  · exact u1974

def b3153 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 69 25 248 232 232 232 488), lower := (rows 275 38 69 25 16 32 64 128 256), losses := [] }

theorem u3153 : Upper (D 0) (R 0) [274,36,65,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3153
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 41 216 248 216 216 472), lower := (rows 275 38 69 41 16 32 64 128 256), losses := [] }

theorem u3154 : Upper (D 0) (R 0) [274,36,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3154
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3155 : Route 9 := (fun mask => (mask,id))

def c3155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3155 : Upper (D 0) (R 0) [274,36,65,48] 13 := by
  apply FastRouting.sound _ _ [274,36,65,48] 13 (by decide) (choices 1) [1,8,64,128] r3155 c3155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1975
  · exact u1976
  · exact u1977
  · exact u1978

def b3156 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 69 73 184 184 248 184 440), lower := (rows 275 38 69 73 16 32 64 128 256), losses := [] }

theorem u3156 : Upper (D 0) (R 0) [274,36,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3156
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3157 : Route 9 := (fun mask => (mask,id))

def c3157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3157 : Upper (D 0) (R 0) [274,36,65,80] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80] 13 (by decide) (choices 1) [1,8,32,128] r3157 c3157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1979
  · exact u1980
  · exact u1981
  · exact u1982

def r3158 : Route 9 := (fun mask => (mask,id))

def c3158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3158 : Upper (D 0) (R 0) [274,36,65,96] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96] 13 (by decide) (choices 1) [1,8,128] r3158 c3158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1983
  · exact u1984
  · exact u1985

def r3159 : Route 9 := (fun mask => (mask,id))

def c3159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3159 : Upper (D 0) (R 0) [274,36,65,129] 13 := by
  apply FastRouting.sound _ _ [274,36,65,129] 13 (by decide) (choices 1) [8,32,64,128] r3159 c3159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1986
  · exact u1987
  · exact u1988
  · exact u1989

def r3160 : Route 9 := (fun mask => (mask,id))

def c3160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3160 : Upper (D 0) (R 0) [274,36,65,144] 13 := by
  apply FastRouting.sound _ _ [274,36,65,144] 13 (by decide) (choices 1) [1,8,32,64,128] r3160 c3160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1990
  · exact u1991
  · exact u1992
  · exact u1993
  · exact u1994

def r3161 : Route 9 := (fun mask => (mask,id))

def c3161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3161 : Upper (D 0) (R 0) [274,36,65,160] 13 := by
  apply FastRouting.sound _ _ [274,36,65,160] 13 (by decide) (choices 1) [1,8,64,128] r3161 c3161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1995
  · exact u1996
  · exact u1997
  · exact u1998

def r3162 : Route 9 := (fun mask => (mask,id))

def c3162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3162 : Upper (D 0) (R 0) [274,36,65,192] 13 := by
  apply FastRouting.sound _ _ [274,36,65,192] 13 (by decide) (choices 1) [1,8,32,128] r3162 c3162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1999
  · exact u2000
  · exact u2001
  · exact u2002

def b3163 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 76 25 241 225 225 225 481), lower := (rows 275 38 76 25 16 32 64 128 256), losses := [] }

theorem u3163 : Upper (D 0) (R 0) [274,36,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3163
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 41 209 241 209 209 465), lower := (rows 275 38 76 41 16 32 64 128 256), losses := [] }

theorem u3164 : Upper (D 0) (R 0) [274,36,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3164
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 56 209 225 193 193 449), lower := (rows 275 38 76 56 16 32 64 128 256), losses := [] }

theorem u3165 : Upper (D 0) (R 0) [274,36,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3165
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 38 76 73 177 177 241 177 433), lower := (rows 275 38 76 73 16 32 64 128 256), losses := [] }

theorem u3166 : Upper (D 0) (R 0) [274,36,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3166
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3167 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 38 76 88 177 161 225 161 417), lower := (rows 275 38 76 88 16 32 64 128 256), losses := [] }

theorem u3167 : Upper (D 0) (R 0) [274,36,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3167
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3168 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 76 104 145 177 209 145 401), lower := (rows 275 38 76 104 16 32 64 128 256), losses := [] }

theorem u3168 : Upper (D 0) (R 0) [274,36,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3168
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3169 : Route 9 := (fun mask => (mask,id))

def c3169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3169 : Upper (D 0) (R 0) [274,36,72,129] 13 := by
  apply FastRouting.sound _ _ [274,36,72,129] 13 (by decide) (choices 1) [1,32,64,128] r3169 c3169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2003
  · exact u2004
  · exact u2005
  · exact u2006

def r3170 : Route 9 := (fun mask => (mask,id))

def c3170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3170 : Upper (D 0) (R 0) [274,36,72,144] 13 := by
  apply FastRouting.sound _ _ [274,36,72,144] 13 (by decide) (choices 1) [1,32,64,128] r3170 c3170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2007
  · exact u2008
  · exact u2009
  · exact u2010

def b3171 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 168 209 241 209 209 465), lower := (rows 275 38 76 168 16 32 64 128 256), losses := [] }

theorem u3171 : Upper (D 0) (R 0) [274,36,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3171
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3172 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 38 76 200 177 177 241 177 433), lower := (rows 275 38 76 200 16 32 64 128 256), losses := [] }

theorem u3172 : Upper (D 0) (R 0) [274,36,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3172
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 196 25 249 233 233 233 489), lower := (rows 275 38 196 25 16 32 64 128 256), losses := [] }

theorem u3173 : Upper (D 0) (R 0) [274,36,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3173
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 196 41 217 249 217 217 473), lower := (rows 275 38 196 41 16 32 64 128 256), losses := [] }

theorem u3174 : Upper (D 0) (R 0) [274,36,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3174
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3175 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3175 : Upper (D 0) (R 0) [274,36,192,48] 13 := by
  apply FastRouting.sound _ _ [274,36,192,48] 13 (by decide) (choices 1) [1,8,64] r3175 c3175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2011
  · exact u2012
  · exact u2013

def r3176 : Route 9 := (fun mask => (mask,id))

def c3176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3176 : Upper (D 0) (R 0) [274,36,192,65] 13 := by
  apply FastRouting.sound _ _ [274,36,192,65] 13 (by decide) (choices 1) [1,8,32,128] r3176 c3176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2014
  · exact u2015
  · exact u2016
  · exact u2017

def r3177 : Route 9 := (fun mask => (mask,id))

def c3177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3177 : Upper (D 0) (R 0) [274,36,192,80] 13 := by
  apply FastRouting.sound _ _ [274,36,192,80] 13 (by decide) (choices 1) [1,8,32,128] r3177 c3177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2018
  · exact u2019
  · exact u2020
  · exact u2021

def r3178 : Route 9 := (fun mask => (mask,id))

def c3178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3178 : Upper (D 0) (R 0) [274,36,192,96] 13 := by
  apply FastRouting.sound _ _ [274,36,192,96] 13 (by decide) (choices 1) [1,8,128] r3178 c3178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2022
  · exact u2023
  · exact u2024

def b3179 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 196 200 57 57 121 185 313), lower := (rows 275 38 196 200 16 32 64 128 256), losses := [] }

theorem u3179 : Upper (D 0) (R 0) [274,36,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3179
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P00
