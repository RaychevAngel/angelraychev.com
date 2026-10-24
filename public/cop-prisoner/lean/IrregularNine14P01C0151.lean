import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0115
import IrregularNine14P01C0116
import IrregularNine14P01C0117
import IrregularNine14P01C0118
import IrregularNine14P01C0119

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9060 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 424, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 13 490 498 482 482 482 482), lower := (rows 53 82 13 8 16 32 64 128 256), losses := [] }

theorem u9060 : Upper (D 1) (R 1) [52,80,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9061 : Route 9 := (fun mask => (mask,id))

def c9061 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9061 : Upper (D 1) (R 1) [52,80,10] 13 := by
  apply FastRouting.sound _ _ [52,80,10] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r9061 c9061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6959
  · exact u6960
  · exact u6961
  · exact u6962
  · exact u6963
  · exact u6964
  · exact u6965
  · exact u6966
  · exact u6967
  · exact u6968
  · exact u6969
  · exact u6970
  · exact u6971
  · exact u6972
  · exact u6973

def b9062 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 37 458 474 490 458 458 458), lower := (rows 53 82 37 8 16 32 64 128 256), losses := [] }

theorem u9062 : Upper (D 1) (R 1) [52,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9063 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 38 459 475 491 459 459 459), lower := (rows 53 82 38 8 16 32 64 128 256), losses := [] }

theorem u9063 : Upper (D 1) (R 1) [52,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9064 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 44 459 467 483 451 451 451), lower := (rows 53 82 44 8 16 32 64 128 256), losses := [] }

theorem u9064 : Upper (D 1) (R 1) [52,80,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9065 : PairBound 9 := { available := 426, camps := [{ cop := 1, region := 424, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 69 426 442 426 490 426 426), lower := (rows 53 82 69 8 16 32 64 128 256), losses := [] }

theorem u9065 : Upper (D 1) (R 1) [52,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9066 : PairBound 9 := { available := 427, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 70 427 443 427 491 427 427), lower := (rows 53 82 70 8 16 32 64 128 256), losses := [] }

theorem u9066 : Upper (D 1) (R 1) [52,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9067 : Route 9 := (fun mask => (mask,id))

def c9067 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 65 => 6 | 6 => 2 | 18 => 4 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9067 : Upper (D 1) (R 1) [52,80,72] 13 := by
  apply FastRouting.sound _ _ [52,80,72] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r9067 c9067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6974
  · exact u6975
  · exact u6976
  · exact u6977
  · exact u6978
  · exact u6979
  · exact u6980
  · exact u6981
  · exact u6982
  · exact u6983

def b9068 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 100 395 411 427 459 395 395), lower := (rows 53 82 100 8 16 32 64 128 256), losses := [] }

theorem u9068 : Upper (D 1) (R 1) [52,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9069 : PairBound 9 := { available := 490, camps := [{ cop := 1, region := 424, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 133 490 506 490 490 490 490), lower := (rows 53 82 133 8 16 32 64 128 256), losses := [] }

theorem u9069 : Upper (D 1) (R 1) [52,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9070 : Route 9 := (fun mask => (mask,id))

def c9070 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9070 : Upper (D 1) (R 1) [52,80,130] 13 := by
  apply FastRouting.sound _ _ [52,80,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r9070 c9070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6984
  · exact u6985
  · exact u6986
  · exact u6987
  · exact u6988
  · exact u6989
  · exact u6990
  · exact u6991
  · exact u6992
  · exact u6993
  · exact u6994
  · exact u6995
  · exact u6996
  · exact u6997
  · exact u6998

def r9071 : Route 9 := (fun mask => (mask,id))

def c9071 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9071 : Upper (D 1) (R 1) [52,80,136] 13 := by
  apply FastRouting.sound _ _ [52,80,136] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r9071 c9071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6999
  · exact u7000
  · exact u7001
  · exact u7002
  · exact u7003
  · exact u7004
  · exact u7005
  · exact u7006
  · exact u7007
  · exact u7008
  · exact u7009
  · exact u7010
  · exact u7011
  · exact u7012
  · exact u7013

def b9072 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 164 459 475 491 459 459 459), lower := (rows 53 82 164 8 16 32 64 128 256), losses := [] }

theorem u9072 : Upper (D 1) (R 1) [52,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9073 : Route 9 := (fun mask => (mask,id))

def c9073 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 65 => 6 | 6 => 2 | 18 => 4 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9073 : Upper (D 1) (R 1) [52,80,192] 13 := by
  apply FastRouting.sound _ _ [52,80,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r9073 c9073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7014
  · exact u7015
  · exact u7016
  · exact u7017
  · exact u7018
  · exact u7019
  · exact u7020
  · exact u7021
  · exact u7022
  · exact u7023

def b9074 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 261 234 250 234 234 234 490), lower := (rows 53 82 261 8 16 32 64 128 256), losses := [] }

theorem u9074 : Upper (D 1) (R 1) [52,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9075 : Route 9 := (fun mask => (mask,id))

def c9075 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9075 : Upper (D 1) (R 1) [52,80,258] 13 := by
  apply FastRouting.sound _ _ [52,80,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9075 c9075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7024
  · exact u7025
  · exact u7026
  · exact u7027
  · exact u7028
  · exact u7029
  · exact u7030
  · exact u7031
  · exact u7032
  · exact u7033

def r9076 : Route 9 := (fun mask => (mask,id))

def c9076 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9076 : Upper (D 1) (R 1) [52,80,264] 13 := by
  apply FastRouting.sound _ _ [52,80,264] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9076 c9076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7034
  · exact u7035
  · exact u7036
  · exact u7037
  · exact u7038
  · exact u7039
  · exact u7040
  · exact u7041
  · exact u7042
  · exact u7043

def b9077 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 292 203 219 235 203 203 459), lower := (rows 53 82 292 8 16 32 64 128 256), losses := [] }

theorem u9077 : Upper (D 1) (R 1) [52,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9078 : Route 9 := (fun mask => (mask,id))

def c9078 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 65 => 6 | 257 => 8 | 6 => 2 | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9078 : Upper (D 1) (R 1) [52,80,320] 13 := by
  apply FastRouting.sound _ _ [52,80,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r9078 c9078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7044
  · exact u7045
  · exact u7046
  · exact u7047
  · exact u7048
  · exact u7049

def r9079 : Route 9 := (fun mask => (mask,id))

def c9079 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9079 : Upper (D 1) (R 1) [52,80,384] 13 := by
  apply FastRouting.sound _ _ [52,80,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9079 c9079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7050
  · exact u7051
  · exact u7052
  · exact u7053
  · exact u7054
  · exact u7055
  · exact u7056
  · exact u7057
  · exact u7058
  · exact u7059

def r9080 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9080 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9080 : Upper (D 1) (R 1) [52,192,3] 13 := by
  apply FastRouting.sound _ _ [52,192,3] 13 (by decide) (choices 2) [18,48,66,80,192,258,272,320] r9080 c9080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7060
  · exact u7061
  · exact u7062
  · exact u7063
  · exact u7064
  · exact u7065
  · exact u7066
  · exact u7067

def r9081 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9081 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9081 : Upper (D 1) (R 1) [52,192,9] 13 := by
  apply FastRouting.sound _ _ [52,192,9] 13 (by decide) (choices 2) [18,48,66,80,192,258,272,320] r9081 c9081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7068
  · exact u7069
  · exact u7070
  · exact u7071
  · exact u7072
  · exact u7073
  · exact u7074
  · exact u7075

def r9082 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9082 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9082 : Upper (D 1) (R 1) [52,192,10] 13 := by
  apply FastRouting.sound _ _ [52,192,10] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320] r9082 c9082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7076
  · exact u7077
  · exact u7078
  · exact u7079
  · exact u7080
  · exact u7081
  · exact u7082
  · exact u7083
  · exact u7084
  · exact u7085
  · exact u7086
  · exact u7087

def b9083 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 21 490 506 490 490 490 490), lower := (rows 53 194 21 8 16 32 64 128 256), losses := [] }

theorem u9083 : Upper (D 1) (R 1) [52,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9084 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 22 491 507 491 491 491 491), lower := (rows 53 194 22 8 16 32 64 128 256), losses := [] }

theorem u9084 : Upper (D 1) (R 1) [52,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9085 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 28 491 499 483 483 483 483), lower := (rows 53 194 28 8 16 32 64 128 256), losses := [] }

theorem u9085 : Upper (D 1) (R 1) [52,192,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9086 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 52 459 475 491 459 459 459), lower := (rows 53 194 52 8 16 32 64 128 256), losses := [] }

theorem u9086 : Upper (D 1) (R 1) [52,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9087 : PairBound 9 := { available := 442, camps := [{ cop := 1, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 53 194 69 442 442 442 506 442 442), lower := (rows 53 194 69 8 16 32 64 128 256), losses := [] }

theorem u9087 : Upper (D 1) (R 1) [52,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9088 : PairBound 9 := { available := 443, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 70 443 443 443 507 443 443), lower := (rows 53 194 70 8 16 32 64 128 256), losses := [] }

theorem u9088 : Upper (D 1) (R 1) [52,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9089 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9089 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9089 : Upper (D 1) (R 1) [52,192,72] 13 := by
  apply FastRouting.sound _ _ [52,192,72] 13 (by decide) (choices 2) [3,17,18,48,129,130,144,257,258,272,384] r9089 c9089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7088
  · exact u7089
  · exact u7090
  · exact u7091
  · exact u7092
  · exact u7093
  · exact u7094
  · exact u7095
  · exact u7096
  · exact u7097
  · exact u7098

def b9090 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 84 427 443 427 491 427 427), lower := (rows 53 194 84 8 16 32 64 128 256), losses := [] }

theorem u9090 : Upper (D 1) (R 1) [52,192,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9091 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 196 315 315 315 379 443 315), lower := (rows 53 194 196 8 16 32 64 128 256), losses := [] }

theorem u9091 : Upper (D 1) (R 1) [52,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9092 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9092 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9092 : Upper (D 1) (R 1) [52,192,257] 13 := by
  apply FastRouting.sound _ _ [52,192,257] 13 (by decide) (choices 2) [18,48,66,80,192] r9092 c9092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7099
  · exact u7100
  · exact u7101
  · exact u7102
  · exact u7103

def r9093 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9093 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9093 : Upper (D 1) (R 1) [52,192,258] 13 := by
  apply FastRouting.sound _ _ [52,192,258] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9093 c9093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7104
  · exact u7105
  · exact u7106
  · exact u7107
  · exact u7108
  · exact u7109
  · exact u7110
  · exact u7111

def r9094 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9094 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9094 : Upper (D 1) (R 1) [52,192,264] 13 := by
  apply FastRouting.sound _ _ [52,192,264] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9094 c9094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7112
  · exact u7113
  · exact u7114
  · exact u7115
  · exact u7116
  · exact u7117
  · exact u7118
  · exact u7119

def b9095 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 276 235 251 235 235 235 491), lower := (rows 53 194 276 8 16 32 64 128 256), losses := [] }

theorem u9095 : Upper (D 1) (R 1) [52,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9096 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9096 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9096 : Upper (D 1) (R 1) [52,192,320] 13 := by
  apply FastRouting.sound _ _ [52,192,320] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9096 c9096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7120
  · exact u7121
  · exact u7122
  · exact u7123
  · exact u7124
  · exact u7125
  · exact u7126

def r9097 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9097 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9097 : Upper (D 1) (R 1) [52,257,10] 13 := by
  apply FastRouting.sound _ _ [52,257,10] 13 (by decide) (choices 2) [18,48,66,80,192] r9097 c9097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7127
  · exact u7128
  · exact u7129
  · exact u7130
  · exact u7131

def b9098 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 22 234 250 234 234 234 490), lower := (rows 53 259 22 8 16 32 64 128 256), losses := [] }

theorem u9098 : Upper (D 1) (R 1) [52,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9099 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 28 234 242 226 226 226 482), lower := (rows 53 259 28 8 16 32 64 128 256), losses := [] }

theorem u9099 : Upper (D 1) (R 1) [52,257,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9100 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 259 52 202 218 234 202 202 458), lower := (rows 53 259 52 8 16 32 64 128 256), losses := [] }

theorem u9100 : Upper (D 1) (R 1) [52,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9101 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9101 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9101 : Upper (D 1) (R 1) [52,257,66] 13 := by
  apply FastRouting.sound _ _ [52,257,66] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9101 c9101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7132
  · exact u7133
  · exact u7134
  · exact u7135
  · exact u7136
  · exact u7137
  · exact u7138

def r9102 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9102 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9102 : Upper (D 1) (R 1) [52,257,72] 13 := by
  apply FastRouting.sound _ _ [52,257,72] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9102 c9102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7139
  · exact u7140
  · exact u7141
  · exact u7142
  · exact u7143
  · exact u7144
  · exact u7145

def b9103 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 84 234 250 234 234 234 490), lower := (rows 53 259 84 8 16 32 64 128 256), losses := [] }

theorem u9103 : Upper (D 1) (R 1) [52,257,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9104 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9104 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9104 : Upper (D 1) (R 1) [52,257,192] 13 := by
  apply FastRouting.sound _ _ [52,257,192] 13 (by decide) (choices 2) [18,48,66,80,192] r9104 c9104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7146
  · exact u7147
  · exact u7148
  · exact u7149
  · exact u7150

def r9105 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9105 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9105 : Upper (D 1) (R 1) [52,264,3] 13 := by
  apply FastRouting.sound _ _ [52,264,3] 13 (by decide) (choices 2) [18,48,66,80,192] r9105 c9105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7151
  · exact u7152
  · exact u7153
  · exact u7154
  · exact u7155

def b9106 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 266 21 234 242 226 226 226 482), lower := (rows 53 266 21 8 16 32 64 128 256), losses := [] }

theorem u9106 : Upper (D 1) (R 1) [52,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9107 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 22 235 243 227 227 227 483), lower := (rows 53 266 22 8 16 32 64 128 256), losses := [] }

theorem u9107 : Upper (D 1) (R 1) [52,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9108 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 266 52 203 211 227 195 195 451), lower := (rows 53 266 52 8 16 32 64 128 256), losses := [] }

theorem u9108 : Upper (D 1) (R 1) [52,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9109 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9109 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9109 : Upper (D 1) (R 1) [52,264,65] 13 := by
  apply FastRouting.sound _ _ [52,264,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9109 c9109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7156
  · exact u7157
  · exact u7158
  · exact u7159
  · exact u7160
  · exact u7161
  · exact u7162

def r9110 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9110 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9110 : Upper (D 1) (R 1) [52,264,66] 13 := by
  apply FastRouting.sound _ _ [52,264,66] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9110 c9110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7163
  · exact u7164
  · exact u7165
  · exact u7166
  · exact u7167
  · exact u7168
  · exact u7169
  · exact u7170
  · exact u7171
  · exact u7172
  · exact u7173

def b9111 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 84 235 243 227 227 227 483), lower := (rows 53 266 84 8 16 32 64 128 256), losses := [] }

theorem u9111 : Upper (D 1) (R 1) [52,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9112 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9112 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9112 : Upper (D 1) (R 1) [52,264,192] 13 := by
  apply FastRouting.sound _ _ [52,264,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9112 c9112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7174
  · exact u7175
  · exact u7176
  · exact u7177
  · exact u7178
  · exact u7179
  · exact u7180
  · exact u7181

def b9113 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 53 274 7 234 250 234 234 234 490), lower := (rows 53 274 7 8 16 32 64 128 256), losses := [] }

theorem u9113 : Upper (D 1) (R 1) [52,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9114 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 53 274 13 234 242 226 226 226 482), lower := (rows 53 274 13 8 16 32 64 128 256), losses := [] }

theorem u9114 : Upper (D 1) (R 1) [52,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9115 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9115 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9115 : Upper (D 1) (R 1) [52,272,10] 13 := by
  apply FastRouting.sound _ _ [52,272,10] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9115 c9115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7182
  · exact u7183
  · exact u7184
  · exact u7185
  · exact u7186
  · exact u7187
  · exact u7188

def b9116 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 274 37 202 218 234 202 202 458), lower := (rows 53 274 37 8 16 32 64 128 256), losses := [] }

theorem u9116 : Upper (D 1) (R 1) [52,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9117 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 38 203 219 235 203 203 459), lower := (rows 53 274 38 8 16 32 64 128 256), losses := [] }

theorem u9117 : Upper (D 1) (R 1) [52,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9118 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 44 203 211 227 195 195 451), lower := (rows 53 274 44 8 16 32 64 128 256), losses := [] }

theorem u9118 : Upper (D 1) (R 1) [52,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9119 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 53 274 69 234 250 234 234 234 490), lower := (rows 53 274 69 8 16 32 64 128 256), losses := [] }

theorem u9119 : Upper (D 1) (R 1) [52,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9119
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u9119
end Delivery.IrregularNine14.P01
