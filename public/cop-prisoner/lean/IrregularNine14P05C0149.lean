import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0098
import IrregularNine14P05C0099
import IrregularNine14P05C0100

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8940 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 137 315 299 363 427 299), lower := (rows 7 38 84 137 16 32 64 128 256), losses := [] }

theorem u8940 : Upper (D 5) (R 5) [6,36,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8941 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 138 313 297 361 425 297), lower := (rows 7 38 84 138 16 32 64 128 256), losses := [] }

theorem u8941 : Upper (D 5) (R 5) [6,36,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8942 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 168 283 299 331 395 267), lower := (rows 7 38 84 168 16 32 64 128 256), losses := [] }

theorem u8942 : Upper (D 5) (R 5) [6,36,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8943 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 392 59 43 107 171 299), lower := (rows 7 38 84 392 16 32 64 128 256), losses := [] }

theorem u8943 : Upper (D 5) (R 5) [6,36,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8944 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 100 25 411 427 459 395 395), lower := (rows 7 38 100 25 16 32 64 128 256), losses := [] }

theorem u8944 : Upper (D 5) (R 5) [6,36,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8945 : PairBound 9 := { available := 283, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 100 137 283 315 347 411 283), lower := (rows 7 38 100 137 16 32 64 128 256), losses := [] }

theorem u8945 : Upper (D 5) (R 5) [6,36,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8946 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 100 152 283 299 331 395 267), lower := (rows 7 38 100 152 16 32 64 128 256), losses := [] }

theorem u8946 : Upper (D 5) (R 5) [6,36,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8947 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 100 392 27 59 91 155 283), lower := (rows 7 38 100 392 16 32 64 128 256), losses := [] }

theorem u8947 : Upper (D 5) (R 5) [6,36,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8948 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 25 315 299 363 427 299), lower := (rows 7 38 196 25 16 32 64 128 256), losses := [] }

theorem u8948 : Upper (D 5) (R 5) [6,36,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8949 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 26 313 297 361 425 297), lower := (rows 7 38 196 26 16 32 64 128 256), losses := [] }

theorem u8949 : Upper (D 5) (R 5) [6,36,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8950 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 41 283 315 347 411 283), lower := (rows 7 38 196 41 16 32 64 128 256), losses := [] }

theorem u8950 : Upper (D 5) (R 5) [6,36,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8951 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 56 283 299 331 395 267), lower := (rows 7 38 196 56 16 32 64 128 256), losses := [] }

theorem u8951 : Upper (D 5) (R 5) [6,36,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8952 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 265 59 59 123 187 315), lower := (rows 7 38 196 265 16 32 64 128 256), losses := [] }

theorem u8952 : Upper (D 5) (R 5) [6,36,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8952
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8953 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 266 57 57 121 185 313), lower := (rows 7 38 196 266 16 32 64 128 256), losses := [] }

theorem u8953 : Upper (D 5) (R 5) [6,36,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8954 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 280 59 43 107 171 299), lower := (rows 7 38 196 280 16 32 64 128 256), losses := [] }

theorem u8954 : Upper (D 5) (R 5) [6,36,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8955 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 296 27 59 91 155 283), lower := (rows 7 38 196 296 16 32 64 128 256), losses := [] }

theorem u8955 : Upper (D 5) (R 5) [6,36,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8956 : PairBound 9 := { available := 455, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 44 25 471 487 455 455 455), lower := (rows 7 42 44 25 16 32 64 128 256), losses := [] }

theorem u8956 : Upper (D 5) (R 5) [6,40,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8957 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 464, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 44 26 469 485 453 453 453), lower := (rows 7 42 44 26 16 32 64 128 256), losses := [] }

theorem u8957 : Upper (D 5) (R 5) [6,40,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8958 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 44 73 407 439 471 407 407), lower := (rows 7 42 44 73 16 32 64 128 256), losses := [] }

theorem u8958 : Upper (D 5) (R 5) [6,40,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8959 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 400, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 44 74 405 437 469 405 405), lower := (rows 7 42 44 74 16 32 64 128 256), losses := [] }

theorem u8959 : Upper (D 5) (R 5) [6,40,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8960 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 44 88 407 423 455 391 391), lower := (rows 7 42 44 88 16 32 64 128 256), losses := [] }

theorem u8960 : Upper (D 5) (R 5) [6,40,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8961 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 44 200 279 311 343 407 279), lower := (rows 7 42 44 200 16 32 64 128 256), losses := [] }

theorem u8961 : Upper (D 5) (R 5) [6,40,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8962 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 52 73 415 431 463 399 399), lower := (rows 7 42 52 73 16 32 64 128 256), losses := [] }

theorem u8962 : Upper (D 5) (R 5) [6,40,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8963 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 52 74 413 429 461 397 397), lower := (rows 7 42 52 74 16 32 64 128 256), losses := [] }

theorem u8963 : Upper (D 5) (R 5) [6,40,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8964 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 52 76 411 427 459 395 395), lower := (rows 7 42 52 76 16 32 64 128 256), losses := [] }

theorem u8964 : Upper (D 5) (R 5) [6,40,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8965 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 52 200 287 303 335 399 271), lower := (rows 7 42 52 200 16 32 64 128 256), losses := [] }

theorem u8965 : Upper (D 5) (R 5) [6,40,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8966 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8966 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8966 : Upper (D 5) (R 5) [6,40,65,17] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8966 c8966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5893
  · exact u5894
  · exact u5895
  · exact u5896
  · exact u5897
  · exact u5898
  · exact u5899
  · exact u5900
  · exact u5901
  · exact u5902
  · exact u5903

def r8967 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8967 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8967 : Upper (D 5) (R 5) [6,40,65,18] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8967 c8967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5904
  · exact u5905
  · exact u5906
  · exact u5907
  · exact u5908
  · exact u5909
  · exact u5910
  · exact u5911
  · exact u5912
  · exact u5913
  · exact u5914

def r8968 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8968 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8968 : Upper (D 5) (R 5) [6,40,65,20] 13 := by
  apply FastRouting.sound _ _ [6,40,65,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8968 c8968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5915
  · exact u5916
  · exact u5917
  · exact u5918
  · exact u5919
  · exact u5920
  · exact u5921
  · exact u5922
  · exact u5923
  · exact u5924
  · exact u5925

def b8969 : PairBound 9 := { available := 414, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 41 414 446 478 414 414), lower := (rows 7 42 69 41 16 32 64 128 256), losses := [] }

theorem u8969 : Upper (D 5) (R 5) [6,40,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8970 : PairBound 9 := { available := 413, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 42 413 445 477 413 413), lower := (rows 7 42 69 42 16 32 64 128 256), losses := [] }

theorem u8970 : Upper (D 5) (R 5) [6,40,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8971 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 44 411 443 475 411 411), lower := (rows 7 42 69 44 16 32 64 128 256), losses := [] }

theorem u8971 : Upper (D 5) (R 5) [6,40,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8972 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 56 415 431 463 399 399), lower := (rows 7 42 69 56 16 32 64 128 256), losses := [] }

theorem u8972 : Upper (D 5) (R 5) [6,40,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8973 : Route 9 := (fun mask => (mask,id))

def c8973 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8973 : Upper (D 5) (R 5) [6,40,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8973 c8973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5926
  · exact u5927
  · exact u5928
  · exact u5929
  · exact u5930
  · exact u5931
  · exact u5932
  · exact u5933
  · exact u5934
  · exact u5935

def r8974 : Route 9 := (fun mask => (mask,id))

def c8974 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8974 : Upper (D 5) (R 5) [6,40,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8974 c8974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5936
  · exact u5937
  · exact u5938
  · exact u5939
  · exact u5940
  · exact u5941
  · exact u5942
  · exact u5943
  · exact u5944
  · exact u5945

def r8975 : Route 9 := (fun mask => (mask,id))

def c8975 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8975 : Upper (D 5) (R 5) [6,40,65,132] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8975 c8975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5946
  · exact u5947
  · exact u5948
  · exact u5949
  · exact u5950
  · exact u5951
  · exact u5952
  · exact u5953
  · exact u5954
  · exact u5955

def r8976 : Route 9 := (fun mask => (mask,id))

def c8976 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8976 : Upper (D 5) (R 5) [6,40,65,144] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8976 c8976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5956
  · exact u5957
  · exact u5958
  · exact u5959
  · exact u5960
  · exact u5961
  · exact u5962
  · exact u5963
  · exact u5964
  · exact u5965
  · exact u5966
  · exact u5967
  · exact u5968
  · exact u5969
  · exact u5970

def b8977 : PairBound 9 := { available := 287, camps := [{ cop := 1, region := 341, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 168 287 319 351 415 287), lower := (rows 7 42 69 168 16 32 64 128 256), losses := [] }

theorem u8977 : Upper (D 5) (R 5) [6,40,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8978 : Route 9 := (fun mask => (mask,id))

def c8978 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8978 : Upper (D 5) (R 5) [6,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8978 c8978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5971
  · exact u5972
  · exact u5973
  · exact u5974
  · exact u5975
  · exact u5976
  · exact u5977
  · exact u5978
  · exact u5979
  · exact u5980

def b8979 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 25 445 429 493 429 429), lower := (rows 7 42 70 25 16 32 64 128 256), losses := [] }

theorem u8979 : Upper (D 5) (R 5) [6,40,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8979
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8980 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 28 441 425 489 425 425), lower := (rows 7 42 70 28 16 32 64 128 256), losses := [] }

theorem u8980 : Upper (D 5) (R 5) [6,40,66,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8981 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 137 317 317 381 445 317), lower := (rows 7 42 70 137 16 32 64 128 256), losses := [] }

theorem u8981 : Upper (D 5) (R 5) [6,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8982 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 140 313 313 377 441 313), lower := (rows 7 42 70 140 16 32 64 128 256), losses := [] }

theorem u8982 : Upper (D 5) (R 5) [6,40,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8983 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 152 317 301 365 429 301), lower := (rows 7 42 70 152 16 32 64 128 256), losses := [] }

theorem u8983 : Upper (D 5) (R 5) [6,40,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8984 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 70 392 61 61 125 189 317), lower := (rows 7 42 70 392 16 32 64 128 256), losses := [] }

theorem u8984 : Upper (D 5) (R 5) [6,40,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8985 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8985 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8985 : Upper (D 5) (R 5) [6,40,72,17] 13 := by
  apply FastRouting.sound _ _ [6,40,72,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r8985 c8985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5981
  · exact u5982
  · exact u5983
  · exact u5984
  · exact u5985
  · exact u5986
  · exact u5987
  · exact u5988
  · exact u5989
  · exact u5990
  · exact u5991

def b8986 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 76 26 437 421 485 421 421), lower := (rows 7 42 76 26 16 32 64 128 256), losses := [] }

theorem u8986 : Upper (D 5) (R 5) [6,40,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8987 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 76 28 435 419 483 419 419), lower := (rows 7 42 76 28 16 32 64 128 256), losses := [] }

theorem u8987 : Upper (D 5) (R 5) [6,40,72,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8988 : PairBound 9 := { available := 407, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 41 407 439 471 407 407), lower := (rows 7 42 76 41 16 32 64 128 256), losses := [] }

theorem u8988 : Upper (D 5) (R 5) [6,40,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8989 : PairBound 9 := { available := 405, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 42 405 437 469 405 405), lower := (rows 7 42 76 42 16 32 64 128 256), losses := [] }

theorem u8989 : Upper (D 5) (R 5) [6,40,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8990 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 44 403 435 467 403 403), lower := (rows 7 42 76 44 16 32 64 128 256), losses := [] }

theorem u8990 : Upper (D 5) (R 5) [6,40,72,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8991 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 56 407 423 455 391 391), lower := (rows 7 42 76 56 16 32 64 128 256), losses := [] }

theorem u8991 : Upper (D 5) (R 5) [6,40,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8992 : Route 9 := (fun mask => (mask,id))

def c8992 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8992 : Upper (D 5) (R 5) [6,40,72,129] 13 := by
  apply FastRouting.sound _ _ [6,40,72,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r8992 c8992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5992
  · exact u5993
  · exact u5994
  · exact u5995
  · exact u5996
  · exact u5997
  · exact u5998
  · exact u5999
  · exact u6000
  · exact u6001

def b8993 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 76 138 309 309 373 437 309), lower := (rows 7 42 76 138 16 32 64 128 256), losses := [] }

theorem u8993 : Upper (D 5) (R 5) [6,40,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8994 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 76 140 307 307 371 435 307), lower := (rows 7 42 76 140 16 32 64 128 256), losses := [] }

theorem u8994 : Upper (D 5) (R 5) [6,40,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8994
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8995 : Route 9 := (fun mask => (mask,id))

def c8995 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8995 : Upper (D 5) (R 5) [6,40,72,144] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r8995 c8995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6002
  · exact u6003
  · exact u6004
  · exact u6005
  · exact u6006
  · exact u6007
  · exact u6008
  · exact u6009
  · exact u6010
  · exact u6011

def b8996 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 341, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 168 279 311 343 407 279), lower := (rows 7 42 76 168 16 32 64 128 256), losses := [] }

theorem u8996 : Upper (D 5) (R 5) [6,40,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8997 : Route 9 := (fun mask => (mask,id))

def c8997 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8997 : Upper (D 5) (R 5) [6,40,72,384] 13 := by
  apply FastRouting.sound _ _ [6,40,72,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r8997 c8997
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6012
  · exact u6013
  · exact u6014
  · exact u6015
  · exact u6016
  · exact u6017

def b8998 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 84 41 415 431 463 399 399), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u8998 : Upper (D 5) (R 5) [6,40,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8999 : PairBound 9 := { available := 397, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 42 413 429 461 397 397), lower := (rows 7 42 84 42 16 32 64 128 256), losses := [] }

theorem u8999 : Upper (D 5) (R 5) [6,40,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8999
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8999
end Delivery.IrregularNine14.P05
