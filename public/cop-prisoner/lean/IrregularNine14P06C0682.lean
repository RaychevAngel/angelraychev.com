import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0483
import IrregularNine14P06C0484
import IrregularNine14P06C0485
import IrregularNine14P06C0486
import IrregularNine14P06C0487
import IrregularNine14P06C0488

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40920 : Route 9 := (fun mask => (mask,id))

def c40920 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40920 : Upper (D 6) (R 6) [6,40,144,65] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40920 c40920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29026
  · exact u29027
  · exact u29028
  · exact u29029
  · exact u29030
  · exact u29031
  · exact u29032
  · exact u29033
  · exact u29034
  · exact u29035
  · exact u29036
  · exact u29037
  · exact u29038
  · exact u29039
  · exact u29040

def r40921 : Route 9 := (fun mask => (mask,id))

def c40921 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40921 : Upper (D 6) (R 6) [6,40,144,66] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40921 c40921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29041
  · exact u29042
  · exact u29043
  · exact u29044
  · exact u29045
  · exact u29046
  · exact u29047
  · exact u29048
  · exact u29049
  · exact u29050

def r40922 : Route 9 := (fun mask => (mask,id))

def c40922 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40922 : Upper (D 6) (R 6) [6,40,144,68] 13 := by
  apply FastRouting.sound _ _ [6,40,144,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40922 c40922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29051
  · exact u29052
  · exact u29053
  · exact u29054
  · exact u29055
  · exact u29056
  · exact u29057
  · exact u29058
  · exact u29059
  · exact u29060

def b40923 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 148 104 343 359 327 455 327), lower := (rows 7 42 148 104 16 32 64 128 256), losses := [] }

theorem u40923 : Upper (D 6) (R 6) [6,40,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40924 : Route 9 := (fun mask => (mask,id))

def c40924 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40924 : Upper (D 6) (R 6) [6,40,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40924 c40924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29061
  · exact u29062
  · exact u29063
  · exact u29064
  · exact u29065
  · exact u29066
  · exact u29067
  · exact u29068
  · exact u29069
  · exact u29070

def r40925 : Route 9 := (fun mask => (mask,id))

def c40925 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40925 : Upper (D 6) (R 6) [6,40,144,258] 13 := by
  apply FastRouting.sound _ _ [6,40,144,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40925 c40925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29071
  · exact u29072
  · exact u29073
  · exact u29074
  · exact u29075
  · exact u29076

def r40926 : Route 9 := (fun mask => (mask,id))

def c40926 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40926 : Upper (D 6) (R 6) [6,40,144,260] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40926 c40926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29077
  · exact u29078
  · exact u29079
  · exact u29080
  · exact u29081
  · exact u29082

def b40927 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 148 296 87 103 71 199 327), lower := (rows 7 42 148 296 16 32 64 128 256), losses := [] }

theorem u40927 : Upper (D 6) (R 6) [6,40,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40927
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40928 : Route 9 := (fun mask => (mask,id))

def c40928 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40928 : Upper (D 6) (R 6) [6,40,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40928 c40928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29083
  · exact u29084
  · exact u29085
  · exact u29086
  · exact u29087
  · exact u29088
  · exact u29089
  · exact u29090
  · exact u29091
  · exact u29092

def b40929 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 164 11 341 373 341 469 341), lower := (rows 7 42 164 11 16 32 64 128 256), losses := [] }

theorem u40929 : Upper (D 6) (R 6) [6,40,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40930 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 164 13 339 371 339 467 339), lower := (rows 7 42 164 13 16 32 64 128 256), losses := [] }

theorem u40930 : Upper (D 6) (R 6) [6,40,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40931 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 164 14 337 369 337 465 337), lower := (rows 7 42 164 14 16 32 64 128 256), losses := [] }

theorem u40931 : Upper (D 6) (R 6) [6,40,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40932 : Route 9 := (fun mask => (mask,id))

def c40932 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40932 : Upper (D 6) (R 6) [6,40,160,17] 13 := by
  apply FastRouting.sound _ _ [6,40,160,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40932 c40932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29093
  · exact u29094
  · exact u29095
  · exact u29096
  · exact u29097
  · exact u29098
  · exact u29099
  · exact u29100
  · exact u29101
  · exact u29102

def b40933 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 344, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 164 26 341 357 325 453 325), lower := (rows 7 42 164 26 16 32 64 128 256), losses := [] }

theorem u40933 : Upper (D 6) (R 6) [6,40,160,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40934 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 164 28 339 355 323 451 323), lower := (rows 7 42 164 28 16 32 64 128 256), losses := [] }

theorem u40934 : Upper (D 6) (R 6) [6,40,160,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40935 : Route 9 := (fun mask => (mask,id))

def c40935 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40935 : Upper (D 6) (R 6) [6,40,160,65] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40935 c40935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29103
  · exact u29104
  · exact u29105
  · exact u29106
  · exact u29107
  · exact u29108
  · exact u29109
  · exact u29110
  · exact u29111
  · exact u29112

def b40936 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 344, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 164 74 341 373 341 469 341), lower := (rows 7 42 164 74 16 32 64 128 256), losses := [] }

theorem u40936 : Upper (D 6) (R 6) [6,40,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40937 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 164 76 339 371 339 467 339), lower := (rows 7 42 164 76 16 32 64 128 256), losses := [] }

theorem u40937 : Upper (D 6) (R 6) [6,40,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40938 : Route 9 := (fun mask => (mask,id))

def c40938 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40938 : Upper (D 6) (R 6) [6,40,160,80] 13 := by
  apply FastRouting.sound _ _ [6,40,160,80] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40938 c40938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29113
  · exact u29114
  · exact u29115
  · exact u29116
  · exact u29117
  · exact u29118
  · exact u29119
  · exact u29120
  · exact u29121
  · exact u29122

def r40939 : Route 9 := (fun mask => (mask,id))

def c40939 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40939 : Upper (D 6) (R 6) [6,40,160,257] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40939 c40939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29123
  · exact u29124
  · exact u29125
  · exact u29126
  · exact u29127
  · exact u29128

def b40940 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 344, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 164 266 85 117 85 213 341), lower := (rows 7 42 164 266 16 32 64 128 256), losses := [] }

theorem u40940 : Upper (D 6) (R 6) [6,40,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40941 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 164 268 83 115 83 211 339), lower := (rows 7 42 164 268 16 32 64 128 256), losses := [] }

theorem u40941 : Upper (D 6) (R 6) [6,40,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40941
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40942 : Route 9 := (fun mask => (mask,id))

def c40942 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40942 : Upper (D 6) (R 6) [6,40,160,272] 13 := by
  apply FastRouting.sound _ _ [6,40,160,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40942 c40942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29129
  · exact u29130
  · exact u29131
  · exact u29132
  · exact u29133
  · exact u29134

def r40943 : Route 9 := (fun mask => (mask,id))

def c40943 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40943 : Upper (D 6) (R 6) [6,40,160,320] 13 := by
  apply FastRouting.sound _ _ [6,40,160,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40943 c40943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29135
  · exact u29136
  · exact u29137
  · exact u29138
  · exact u29139
  · exact u29140

def b40944 : PairBound 9 := { available := 373, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 196 11 373 373 373 501 373), lower := (rows 7 42 196 11 16 32 64 128 256), losses := [] }

theorem u40944 : Upper (D 6) (R 6) [6,40,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40945 : PairBound 9 := { available := 371, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 196 13 371 371 371 499 371), lower := (rows 7 42 196 13 16 32 64 128 256), losses := [] }

theorem u40945 : Upper (D 6) (R 6) [6,40,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40945
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40946 : PairBound 9 := { available := 369, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 196 14 369 369 369 497 369), lower := (rows 7 42 196 14 16 32 64 128 256), losses := [] }

theorem u40946 : Upper (D 6) (R 6) [6,40,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40946
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40947 : Route 9 := (fun mask => (mask,id))

def c40947 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40947 : Upper (D 6) (R 6) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40947 c40947
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29141
  · exact u29142
  · exact u29143
  · exact u29144
  · exact u29145
  · exact u29146
  · exact u29147
  · exact u29148
  · exact u29149
  · exact u29150
  · exact u29151
  · exact u29152
  · exact u29153
  · exact u29154
  · exact u29155

def r40948 : Route 9 := (fun mask => (mask,id))

def c40948 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40948 : Upper (D 6) (R 6) [6,40,192,18] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40948 c40948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29156
  · exact u29157
  · exact u29158
  · exact u29159
  · exact u29160
  · exact u29161
  · exact u29162
  · exact u29163
  · exact u29164
  · exact u29165

def r40949 : Route 9 := (fun mask => (mask,id))

def c40949 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40949 : Upper (D 6) (R 6) [6,40,192,20] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40949 c40949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29166
  · exact u29167
  · exact u29168
  · exact u29169
  · exact u29170
  · exact u29171
  · exact u29172
  · exact u29173
  · exact u29174
  · exact u29175

def b40950 : PairBound 9 := { available := 343, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 196 41 343 375 343 471 343), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u40950 : Upper (D 6) (R 6) [6,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40950
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40951 : PairBound 9 := { available := 341, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 42 341 373 341 469 341), lower := (rows 7 42 196 42 16 32 64 128 256), losses := [] }

theorem u40951 : Upper (D 6) (R 6) [6,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40951
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40952 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 196 44 339 371 339 467 339), lower := (rows 7 42 196 44 16 32 64 128 256), losses := [] }

theorem u40952 : Upper (D 6) (R 6) [6,40,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40952
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40953 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 196 56 343 359 327 455 327), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u40953 : Upper (D 6) (R 6) [6,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40953
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40954 : Route 9 := (fun mask => (mask,id))

def c40954 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40954 : Upper (D 6) (R 6) [6,40,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r40954 c40954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29176
  · exact u29177
  · exact u29178
  · exact u29179
  · exact u29180
  · exact u29181
  · exact u29182
  · exact u29183
  · exact u29184
  · exact u29185

def b40955 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 304, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 196 74 309 309 373 437 309), lower := (rows 7 42 196 74 16 32 64 128 256), losses := [] }

theorem u40955 : Upper (D 6) (R 6) [6,40,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40955
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40956 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 196 76 307 307 371 435 307), lower := (rows 7 42 196 76 16 32 64 128 256), losses := [] }

theorem u40956 : Upper (D 6) (R 6) [6,40,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40957 : Route 9 := (fun mask => (mask,id))

def c40957 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40957 : Upper (D 6) (R 6) [6,40,192,80] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r40957 c40957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29186
  · exact u29187
  · exact u29188
  · exact u29189
  · exact u29190
  · exact u29191
  · exact u29192
  · exact u29193
  · exact u29194
  · exact u29195

def b40958 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 196 104 279 311 343 407 279), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u40958 : Upper (D 6) (R 6) [6,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40959 : Route 9 := (fun mask => (mask,id))

def c40959 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40959 : Upper (D 6) (R 6) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40959 c40959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29196
  · exact u29197
  · exact u29198
  · exact u29199
  · exact u29200
  · exact u29201
  · exact u29202
  · exact u29203
  · exact u29204
  · exact u29205

def r40960 : Route 9 := (fun mask => (mask,id))

def c40960 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40960 : Upper (D 6) (R 6) [6,40,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40960 c40960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29206
  · exact u29207
  · exact u29208
  · exact u29209
  · exact u29210
  · exact u29211

def r40961 : Route 9 := (fun mask => (mask,id))

def c40961 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40961 : Upper (D 6) (R 6) [6,40,192,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40961 c40961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29212
  · exact u29213
  · exact u29214
  · exact u29215
  · exact u29216
  · exact u29217

def r40962 : Route 9 := (fun mask => (mask,id))

def c40962 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40962 : Upper (D 6) (R 6) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40962 c40962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29218
  · exact u29219
  · exact u29220
  · exact u29221
  · exact u29222
  · exact u29223
  · exact u29224
  · exact u29225
  · exact u29226
  · exact u29227

def b40963 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 196 296 87 119 87 215 343), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u40963 : Upper (D 6) (R 6) [6,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40964 : Route 9 := (fun mask => (mask,id))

def c40964 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40964 : Upper (D 6) (R 6) [6,40,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r40964 c40964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29228
  · exact u29229
  · exact u29230
  · exact u29231
  · exact u29232
  · exact u29233

def b40965 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 388 11 117 117 117 245 373), lower := (rows 7 42 388 11 16 32 64 128 256), losses := [] }

theorem u40965 : Upper (D 6) (R 6) [6,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40966 : PairBound 9 := { available := 115, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 388 13 115 115 115 243 371), lower := (rows 7 42 388 13 16 32 64 128 256), losses := [] }

theorem u40966 : Upper (D 6) (R 6) [6,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40966
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40967 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 388 14 113 113 113 241 369), lower := (rows 7 42 388 14 16 32 64 128 256), losses := [] }

theorem u40967 : Upper (D 6) (R 6) [6,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40968 : Route 9 := (fun mask => (mask,id))

def c40968 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40968 : Upper (D 6) (R 6) [6,40,384,17] 13 := by
  apply FastRouting.sound _ _ [6,40,384,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40968 c40968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29234
  · exact u29235
  · exact u29236
  · exact u29237
  · exact u29238
  · exact u29239
  · exact u29240
  · exact u29241
  · exact u29242
  · exact u29243

def r40969 : Route 9 := (fun mask => (mask,id))

def c40969 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40969 : Upper (D 6) (R 6) [6,40,384,18] 13 := by
  apply FastRouting.sound _ _ [6,40,384,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40969 c40969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29244
  · exact u29245
  · exact u29246
  · exact u29247
  · exact u29248
  · exact u29249

def r40970 : Route 9 := (fun mask => (mask,id))

def c40970 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40970 : Upper (D 6) (R 6) [6,40,384,20] 13 := by
  apply FastRouting.sound _ _ [6,40,384,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40970 c40970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29250
  · exact u29251
  · exact u29252
  · exact u29253
  · exact u29254
  · exact u29255

def b40971 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 388 41 87 119 87 215 343), lower := (rows 7 42 388 41 16 32 64 128 256), losses := [] }

theorem u40971 : Upper (D 6) (R 6) [6,40,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40971
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40972 : PairBound 9 := { available := 85, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 42 85 117 85 213 341), lower := (rows 7 42 388 42 16 32 64 128 256), losses := [] }

theorem u40972 : Upper (D 6) (R 6) [6,40,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40973 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 388 44 83 115 83 211 339), lower := (rows 7 42 388 44 16 32 64 128 256), losses := [] }

theorem u40973 : Upper (D 6) (R 6) [6,40,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40974 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 388 56 87 103 71 199 327), lower := (rows 7 42 388 56 16 32 64 128 256), losses := [] }

theorem u40974 : Upper (D 6) (R 6) [6,40,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40975 : Route 9 := (fun mask => (mask,id))

def c40975 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40975 : Upper (D 6) (R 6) [6,40,384,65] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40975 c40975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29256
  · exact u29257
  · exact u29258
  · exact u29259
  · exact u29260
  · exact u29261
  · exact u29262
  · exact u29263
  · exact u29264
  · exact u29265

def r40976 : Route 9 := (fun mask => (mask,id))

def c40976 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40976 : Upper (D 6) (R 6) [6,40,384,66] 13 := by
  apply FastRouting.sound _ _ [6,40,384,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40976 c40976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29266
  · exact u29267
  · exact u29268
  · exact u29269
  · exact u29270
  · exact u29271

def r40977 : Route 9 := (fun mask => (mask,id))

def c40977 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40977 : Upper (D 6) (R 6) [6,40,384,68] 13 := by
  apply FastRouting.sound _ _ [6,40,384,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40977 c40977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29272
  · exact u29273
  · exact u29274
  · exact u29275
  · exact u29276
  · exact u29277

def r40978 : Route 9 := (fun mask => (mask,id))

def c40978 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40978 : Upper (D 6) (R 6) [6,40,384,80] 13 := by
  apply FastRouting.sound _ _ [6,40,384,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40978 c40978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29278
  · exact u29279
  · exact u29280
  · exact u29281
  · exact u29282
  · exact u29283
  · exact u29284
  · exact u29285
  · exact u29286
  · exact u29287

def b40979 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 388 104 87 119 87 215 343), lower := (rows 7 42 388 104 16 32 64 128 256), losses := [] }

theorem u40979 : Upper (D 6) (R 6) [6,40,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40979
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40979
end Delivery.IrregularNine14.P06
