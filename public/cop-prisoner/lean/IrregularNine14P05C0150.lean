import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0100
import IrregularNine14P05C0101
import IrregularNine14P05C0102
import IrregularNine14P05C0103
import IrregularNine14P05C0104
import IrregularNine14P05C0105

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9000 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 84 44 411 427 459 395 395), lower := (rows 7 42 84 44 16 32 64 128 256), losses := [] }

theorem u9000 : Upper (D 5) (R 5) [6,40,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9001 : Route 9 := (fun mask => (mask,id))

def c9001 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9001 : Upper (D 5) (R 5) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9001 c9001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6018
  · exact u6019
  · exact u6020
  · exact u6021
  · exact u6022
  · exact u6023
  · exact u6024
  · exact u6025
  · exact u6026
  · exact u6027
  · exact u6028
  · exact u6029
  · exact u6030
  · exact u6031
  · exact u6032

def r9002 : Route 9 := (fun mask => (mask,id))

def c9002 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9002 : Upper (D 5) (R 5) [6,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9002 c9002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6033
  · exact u6034
  · exact u6035
  · exact u6036
  · exact u6037
  · exact u6038
  · exact u6039
  · exact u6040
  · exact u6041
  · exact u6042

def r9003 : Route 9 := (fun mask => (mask,id))

def c9003 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9003 : Upper (D 5) (R 5) [6,40,80,132] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9003 c9003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6043
  · exact u6044
  · exact u6045
  · exact u6046
  · exact u6047
  · exact u6048
  · exact u6049
  · exact u6050
  · exact u6051
  · exact u6052

def b9004 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 341, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 84 168 287 303 335 399 271), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u9004 : Upper (D 5) (R 5) [6,40,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9005 : Route 9 := (fun mask => (mask,id))

def c9005 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9005 : Upper (D 5) (R 5) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9005 c9005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6053
  · exact u6054
  · exact u6055
  · exact u6056
  · exact u6057
  · exact u6058
  · exact u6059
  · exact u6060
  · exact u6061
  · exact u6062

def b9006 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 25 415 431 463 399 399), lower := (rows 7 42 100 25 16 32 64 128 256), losses := [] }

theorem u9006 : Upper (D 5) (R 5) [6,40,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9007 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 26 413 429 461 397 397), lower := (rows 7 42 100 26 16 32 64 128 256), losses := [] }

theorem u9007 : Upper (D 5) (R 5) [6,40,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9008 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 28 411 427 459 395 395), lower := (rows 7 42 100 28 16 32 64 128 256), losses := [] }

theorem u9008 : Upper (D 5) (R 5) [6,40,96,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9008
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9009 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 287 319 351 415 287), lower := (rows 7 42 100 137 16 32 64 128 256), losses := [] }

theorem u9009 : Upper (D 5) (R 5) [6,40,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9009
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9010 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 138 285 317 349 413 285), lower := (rows 7 42 100 138 16 32 64 128 256), losses := [] }

theorem u9010 : Upper (D 5) (R 5) [6,40,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9011 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 140 283 315 347 411 283), lower := (rows 7 42 100 140 16 32 64 128 256), losses := [] }

theorem u9011 : Upper (D 5) (R 5) [6,40,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9012 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 152 287 303 335 399 271), lower := (rows 7 42 100 152 16 32 64 128 256), losses := [] }

theorem u9012 : Upper (D 5) (R 5) [6,40,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9013 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 392 31 63 95 159 287), lower := (rows 7 42 100 392 16 32 64 128 256), losses := [] }

theorem u9013 : Upper (D 5) (R 5) [6,40,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9014 : Route 9 := (fun mask => (mask,id))

def c9014 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9014 : Upper (D 5) (R 5) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9014 c9014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6063
  · exact u6064
  · exact u6065
  · exact u6066
  · exact u6067
  · exact u6068
  · exact u6069
  · exact u6070
  · exact u6071
  · exact u6072
  · exact u6073
  · exact u6074
  · exact u6075
  · exact u6076
  · exact u6077

def r9015 : Route 9 := (fun mask => (mask,id))

def c9015 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9015 : Upper (D 5) (R 5) [6,40,192,18] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9015 c9015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6078
  · exact u6079
  · exact u6080
  · exact u6081
  · exact u6082
  · exact u6083
  · exact u6084
  · exact u6085
  · exact u6086
  · exact u6087

def r9016 : Route 9 := (fun mask => (mask,id))

def c9016 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9016 : Upper (D 5) (R 5) [6,40,192,20] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9016 c9016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6088
  · exact u6089
  · exact u6090
  · exact u6091
  · exact u6092
  · exact u6093
  · exact u6094
  · exact u6095
  · exact u6096
  · exact u6097

def b9017 : PairBound 9 := { available := 287, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 41 287 319 351 415 287), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u9017 : Upper (D 5) (R 5) [6,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9018 : PairBound 9 := { available := 285, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 42 285 317 349 413 285), lower := (rows 7 42 196 42 16 32 64 128 256), losses := [] }

theorem u9018 : Upper (D 5) (R 5) [6,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9019 : PairBound 9 := { available := 283, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 44 283 315 347 411 283), lower := (rows 7 42 196 44 16 32 64 128 256), losses := [] }

theorem u9019 : Upper (D 5) (R 5) [6,40,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9019
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9020 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 56 287 303 335 399 271), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u9020 : Upper (D 5) (R 5) [6,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9021 : Route 9 := (fun mask => (mask,id))

def c9021 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9021 : Upper (D 5) (R 5) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9021 c9021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6098
  · exact u6099
  · exact u6100
  · exact u6101
  · exact u6102
  · exact u6103
  · exact u6104
  · exact u6105
  · exact u6106
  · exact u6107

def r9022 : Route 9 := (fun mask => (mask,id))

def c9022 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9022 : Upper (D 5) (R 5) [6,40,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9022 c9022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6108
  · exact u6109
  · exact u6110
  · exact u6111
  · exact u6112
  · exact u6113

def r9023 : Route 9 := (fun mask => (mask,id))

def c9023 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9023 : Upper (D 5) (R 5) [6,40,192,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9023 c9023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6114
  · exact u6115
  · exact u6116
  · exact u6117
  · exact u6118
  · exact u6119

def r9024 : Route 9 := (fun mask => (mask,id))

def c9024 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9024 : Upper (D 5) (R 5) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9024 c9024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6120
  · exact u6121
  · exact u6122
  · exact u6123
  · exact u6124
  · exact u6125
  · exact u6126
  · exact u6127
  · exact u6128
  · exact u6129

def b9025 : PairBound 9 := { available := 31, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 296 31 63 95 159 287), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u9025 : Upper (D 5) (R 5) [6,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9026 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 50 69 14 441 425 489 425 425), lower := (rows 7 50 69 14 16 32 64 128 256), losses := [] }

theorem u9026 : Upper (D 5) (R 5) [6,48,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9027 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9027 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9027 : Upper (D 5) (R 5) [6,48,65,33] 13 := by
  apply FastRouting.sound _ _ [6,48,65,33] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r9027 c9027
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6130
  · exact u6131
  · exact u6132
  · exact u6133
  · exact u6134
  · exact u6135
  · exact u6136

def b9028 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 42 413 429 461 397 397), lower := (rows 7 50 69 42 16 32 64 128 256), losses := [] }

theorem u9028 : Upper (D 5) (R 5) [6,48,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9029 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9029 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9029 : Upper (D 5) (R 5) [6,48,65,36] 13 := by
  apply FastRouting.sound _ _ [6,48,65,36] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r9029 c9029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6137
  · exact u6138
  · exact u6139
  · exact u6140
  · exact u6141
  · exact u6142
  · exact u6143

def r9030 : Route 9 := (fun mask => (mask,id))

def c9030 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9030 : Upper (D 5) (R 5) [6,48,65,129] 13 := by
  apply FastRouting.sound _ _ [6,48,65,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9030 c9030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6144
  · exact u6145
  · exact u6146
  · exact u6147
  · exact u6148
  · exact u6149
  · exact u6150
  · exact u6151
  · exact u6152
  · exact u6153

def r9031 : Route 9 := (fun mask => (mask,id))

def c9031 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9031 : Upper (D 5) (R 5) [6,48,65,130] 13 := by
  apply FastRouting.sound _ _ [6,48,65,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9031 c9031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6154
  · exact u6155
  · exact u6156
  · exact u6157
  · exact u6158
  · exact u6159
  · exact u6160
  · exact u6161
  · exact u6162
  · exact u6163

def r9032 : Route 9 := (fun mask => (mask,id))

def c9032 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9032 : Upper (D 5) (R 5) [6,48,65,132] 13 := by
  apply FastRouting.sound _ _ [6,48,65,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9032 c9032
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6164
  · exact u6165
  · exact u6166
  · exact u6167
  · exact u6168
  · exact u6169
  · exact u6170
  · exact u6171
  · exact u6172
  · exact u6173

def r9033 : Route 9 := (fun mask => (mask,id))

def c9033 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9033 : Upper (D 5) (R 5) [6,48,65,160] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9033 c9033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6174
  · exact u6175
  · exact u6176
  · exact u6177
  · exact u6178
  · exact u6179
  · exact u6180
  · exact u6181
  · exact u6182
  · exact u6183

def r9034 : Route 9 := (fun mask => (mask,id))

def c9034 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9034 : Upper (D 5) (R 5) [6,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,48,65,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9034 c9034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6184
  · exact u6185
  · exact u6186
  · exact u6187
  · exact u6188
  · exact u6189
  · exact u6190
  · exact u6191
  · exact u6192
  · exact u6193

def b9035 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 41 413 429 461 397 397), lower := (rows 7 50 70 41 16 32 64 128 256), losses := [] }

theorem u9035 : Upper (D 5) (R 5) [6,48,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9036 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 44 409 425 457 393 393), lower := (rows 7 50 70 44 16 32 64 128 256), losses := [] }

theorem u9036 : Upper (D 5) (R 5) [6,48,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9036
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9037 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 137 317 301 365 429 301), lower := (rows 7 50 70 137 16 32 64 128 256), losses := [] }

theorem u9037 : Upper (D 5) (R 5) [6,48,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9038 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 140 313 297 361 425 297), lower := (rows 7 50 70 140 16 32 64 128 256), losses := [] }

theorem u9038 : Upper (D 5) (R 5) [6,48,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9039 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 168 285 301 333 397 269), lower := (rows 7 50 70 168 16 32 64 128 256), losses := [] }

theorem u9039 : Upper (D 5) (R 5) [6,48,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9039
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9040 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 70 392 61 45 109 173 301), lower := (rows 7 50 70 392 16 32 64 128 256), losses := [] }

theorem u9040 : Upper (D 5) (R 5) [6,48,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9041 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9041 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9041 : Upper (D 5) (R 5) [6,48,72,33] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r9041 c9041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6194
  · exact u6195
  · exact u6196
  · exact u6197
  · exact u6198
  · exact u6199
  · exact u6200
  · exact u6201
  · exact u6202
  · exact u6203
  · exact u6204

def b9042 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 42 413 429 461 397 397), lower := (rows 7 50 76 42 16 32 64 128 256), losses := [] }

theorem u9042 : Upper (D 5) (R 5) [6,48,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9042
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9043 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9043 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9043 : Upper (D 5) (R 5) [6,48,72,36] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r9043 c9043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6205
  · exact u6206
  · exact u6207
  · exact u6208
  · exact u6209
  · exact u6210
  · exact u6211

def r9044 : Route 9 := (fun mask => (mask,id))

def c9044 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9044 : Upper (D 5) (R 5) [6,48,72,129] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9044 c9044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6212
  · exact u6213
  · exact u6214
  · exact u6215
  · exact u6216
  · exact u6217
  · exact u6218
  · exact u6219
  · exact u6220
  · exact u6221
  · exact u6222
  · exact u6223
  · exact u6224
  · exact u6225
  · exact u6226

def r9045 : Route 9 := (fun mask => (mask,id))

def c9045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9045 : Upper (D 5) (R 5) [6,48,72,130] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9045 c9045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6227
  · exact u6228
  · exact u6229
  · exact u6230
  · exact u6231
  · exact u6232
  · exact u6233
  · exact u6234
  · exact u6235
  · exact u6236

def r9046 : Route 9 := (fun mask => (mask,id))

def c9046 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9046 : Upper (D 5) (R 5) [6,48,72,132] 13 := by
  apply FastRouting.sound _ _ [6,48,72,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9046 c9046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6237
  · exact u6238
  · exact u6239
  · exact u6240
  · exact u6241
  · exact u6242
  · exact u6243
  · exact u6244
  · exact u6245
  · exact u6246

def r9047 : Route 9 := (fun mask => (mask,id))

def c9047 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9047 : Upper (D 5) (R 5) [6,48,72,160] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9047 c9047
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6247
  · exact u6248
  · exact u6249
  · exact u6250
  · exact u6251
  · exact u6252
  · exact u6253
  · exact u6254
  · exact u6255
  · exact u6256

def r9048 : Route 9 := (fun mask => (mask,id))

def c9048 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9048 : Upper (D 5) (R 5) [6,48,72,384] 13 := by
  apply FastRouting.sound _ _ [6,48,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9048 c9048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6257
  · exact u6258
  · exact u6259
  · exact u6260
  · exact u6261
  · exact u6262
  · exact u6263
  · exact u6264
  · exact u6265
  · exact u6266

def b9049 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 100 137 287 303 335 399 271), lower := (rows 7 50 100 137 16 32 64 128 256), losses := [] }

theorem u9049 : Upper (D 5) (R 5) [6,48,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9050 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 100 138 285 301 333 397 269), lower := (rows 7 50 100 138 16 32 64 128 256), losses := [] }

theorem u9050 : Upper (D 5) (R 5) [6,48,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9051 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 100 140 283 299 331 395 267), lower := (rows 7 50 100 140 16 32 64 128 256), losses := [] }

theorem u9051 : Upper (D 5) (R 5) [6,48,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9052 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 100 392 31 47 79 143 271), lower := (rows 7 50 100 392 16 32 64 128 256), losses := [] }

theorem u9052 : Upper (D 5) (R 5) [6,48,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9053 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 50 196 14 313 297 361 425 297), lower := (rows 7 50 196 14 16 32 64 128 256), losses := [] }

theorem u9053 : Upper (D 5) (R 5) [6,48,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9054 : Route 9 := (fun mask => (mask,id))

def c9054 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9054 : Upper (D 5) (R 5) [6,48,192,33] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9054 c9054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6267
  · exact u6268
  · exact u6269
  · exact u6270
  · exact u6271
  · exact u6272
  · exact u6273
  · exact u6274
  · exact u6275
  · exact u6276

def b9055 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 196 42 285 301 333 397 269), lower := (rows 7 50 196 42 16 32 64 128 256), losses := [] }

theorem u9055 : Upper (D 5) (R 5) [6,48,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9056 : Route 9 := (fun mask => (mask,id))

def c9056 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9056 : Upper (D 5) (R 5) [6,48,192,36] 13 := by
  apply FastRouting.sound _ _ [6,48,192,36] 13 (by decide) (choices 2) [3,9,10,257,258,264] r9056 c9056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6277
  · exact u6278
  · exact u6279
  · exact u6280
  · exact u6281
  · exact u6282

def r9057 : Route 9 := (fun mask => (mask,id))

def c9057 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9057 : Upper (D 5) (R 5) [6,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,48,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9057 c9057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6283
  · exact u6284
  · exact u6285
  · exact u6286
  · exact u6287
  · exact u6288
  · exact u6289
  · exact u6290
  · exact u6291
  · exact u6292

def r9058 : Route 9 := (fun mask => (mask,id))

def c9058 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9058 : Upper (D 5) (R 5) [6,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,48,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9058 c9058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6293
  · exact u6294
  · exact u6295
  · exact u6296
  · exact u6297
  · exact u6298

def r9059 : Route 9 := (fun mask => (mask,id))

def c9059 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9059 : Upper (D 5) (R 5) [6,48,192,260] 13 := by
  apply FastRouting.sound _ _ [6,48,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9059 c9059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6299
  · exact u6300
  · exact u6301
  · exact u6302
  · exact u6303
  · exact u6304

#print axioms u9059
end Delivery.IrregularNine14.P05
