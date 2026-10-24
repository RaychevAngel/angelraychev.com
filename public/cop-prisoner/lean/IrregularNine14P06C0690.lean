import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0516
import IrregularNine14P06C0517
import IrregularNine14P06C0518
import IrregularNine14P06C0519
import IrregularNine14P06C0520

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41400 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 196 266 117 117 117 245 373), lower := (rows 11 35 196 266 16 32 64 128 256), losses := [] }

theorem u41400 : Upper (D 6) (R 6) [10,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41401 : Route 9 := (fun mask => (mask,id))

def c41401 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41401 : Upper (D 6) (R 6) [10,33,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41401 c41401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30975
  · exact u30976
  · exact u30977
  · exact u30978
  · exact u30979
  · exact u30980
  · exact u30981
  · exact u30982
  · exact u30983
  · exact u30984

def r41402 : Route 9 := (fun mask => (mask,id))

def c41402 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41402 : Upper (D 6) (R 6) [10,33,192,272] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41402 c41402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30985
  · exact u30986
  · exact u30987
  · exact u30988
  · exact u30989
  · exact u30990
  · exact u30991
  · exact u30992
  · exact u30993
  · exact u30994

def b41403 : PairBound 9 := { available := 87, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 296 87 119 87 215 343), lower := (rows 11 35 196 296 16 32 64 128 256), losses := [] }

theorem u41403 : Upper (D 6) (R 6) [10,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41404 : Route 9 := (fun mask => (mask,id))

def c41404 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41404 : Upper (D 6) (R 6) [10,33,192,320] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r41404 c41404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30995
  · exact u30996
  · exact u30997
  · exact u30998
  · exact u30999
  · exact u31000

def b41405 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 11 116 116 116 244 372), lower := (rows 11 35 388 11 16 32 64 128 256), losses := [] }

theorem u41405 : Upper (D 6) (R 6) [10,33,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41406 : Route 9 := (fun mask => (mask,id))

def c41406 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41406 : Upper (D 6) (R 6) [10,33,384,5] 13 := by
  apply FastRouting.sound _ _ [10,33,384,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41406 c41406
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31001
  · exact u31002
  · exact u31003
  · exact u31004
  · exact u31005
  · exact u31006

def b41407 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 14 117 117 117 245 373), lower := (rows 11 35 388 14 16 32 64 128 256), losses := [] }

theorem u41407 : Upper (D 6) (R 6) [10,33,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41408 : Route 9 := (fun mask => (mask,id))

def c41408 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41408 : Upper (D 6) (R 6) [10,33,384,17] 13 := by
  apply FastRouting.sound _ _ [10,33,384,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41408 c41408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31007
  · exact u31008
  · exact u31009
  · exact u31010
  · exact u31011
  · exact u31012

def b41409 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 26 117 101 101 229 357), lower := (rows 11 35 388 26 16 32 64 128 256), losses := [] }

theorem u41409 : Upper (D 6) (R 6) [10,33,384,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41410 : Route 9 := (fun mask => (mask,id))

def c41410 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41410 : Upper (D 6) (R 6) [10,33,384,20] 13 := by
  apply FastRouting.sound _ _ [10,33,384,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41410 c41410
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31013
  · exact u31014
  · exact u31015
  · exact u31016
  · exact u31017
  · exact u31018
  · exact u31019
  · exact u31020
  · exact u31021
  · exact u31022

def b41411 : PairBound 9 := { available := 86, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 41 86 118 86 214 342), lower := (rows 11 35 388 41 16 32 64 128 256), losses := [] }

theorem u41411 : Upper (D 6) (R 6) [10,33,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41412 : PairBound 9 := { available := 85, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 42 85 117 85 213 341), lower := (rows 11 35 388 42 16 32 64 128 256), losses := [] }

theorem u41412 : Upper (D 6) (R 6) [10,33,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41413 : PairBound 9 := { available := 87, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 44 87 119 87 215 343), lower := (rows 11 35 388 44 16 32 64 128 256), losses := [] }

theorem u41413 : Upper (D 6) (R 6) [10,33,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41414 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 56 87 103 71 199 327), lower := (rows 11 35 388 56 16 32 64 128 256), losses := [] }

theorem u41414 : Upper (D 6) (R 6) [10,33,384,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41415 : Route 9 := (fun mask => (mask,id))

def c41415 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41415 : Upper (D 6) (R 6) [10,33,384,65] 13 := by
  apply FastRouting.sound _ _ [10,33,384,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41415 c41415
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31023
  · exact u31024
  · exact u31025
  · exact u31026
  · exact u31027
  · exact u31028

def b41416 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 388 74 117 117 117 245 373), lower := (rows 11 35 388 74 16 32 64 128 256), losses := [] }

theorem u41416 : Upper (D 6) (R 6) [10,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41417 : Route 9 := (fun mask => (mask,id))

def c41417 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41417 : Upper (D 6) (R 6) [10,33,384,68] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41417 c41417
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31029
  · exact u31030
  · exact u31031
  · exact u31032
  · exact u31033
  · exact u31034
  · exact u31035
  · exact u31036
  · exact u31037
  · exact u31038

def r41418 : Route 9 := (fun mask => (mask,id))

def c41418 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41418 : Upper (D 6) (R 6) [10,33,384,80] 13 := by
  apply FastRouting.sound _ _ [10,33,384,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41418 c41418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31039
  · exact u31040
  · exact u31041
  · exact u31042
  · exact u31043
  · exact u31044
  · exact u31045
  · exact u31046
  · exact u31047
  · exact u31048

def b41419 : PairBound 9 := { available := 87, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 104 87 119 87 215 343), lower := (rows 11 35 388 104 16 32 64 128 256), losses := [] }

theorem u41419 : Upper (D 6) (R 6) [10,33,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41420 : PairBound 9 := { available := 500, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 69 11 500 500 500 500 500), lower := (rows 11 38 69 11 16 32 64 128 256), losses := [] }

theorem u41420 : Upper (D 6) (R 6) [10,36,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41421 : PairBound 9 := { available := 498, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 69 13 498 498 498 498 498), lower := (rows 11 38 69 13 16 32 64 128 256), losses := [] }

theorem u41421 : Upper (D 6) (R 6) [10,36,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41422 : PairBound 9 := { available := 497, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 69 14 497 497 497 497 497), lower := (rows 11 38 69 14 16 32 64 128 256), losses := [] }

theorem u41422 : Upper (D 6) (R 6) [10,36,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41423 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41423 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41423 : Upper (D 6) (R 6) [10,36,65,17] 13 := by
  apply FastRouting.sound _ _ [10,36,65,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r41423 c41423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31049
  · exact u31050
  · exact u31051
  · exact u31052
  · exact u31053
  · exact u31054
  · exact u31055
  · exact u31056
  · exact u31057
  · exact u31058
  · exact u31059

def b41424 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 69 26 501 485 485 485 485), lower := (rows 11 38 69 26 16 32 64 128 256), losses := [] }

theorem u41424 : Upper (D 6) (R 6) [10,36,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41425 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41425 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41425 : Upper (D 6) (R 6) [10,36,65,20] 13 := by
  apply FastRouting.sound _ _ [10,36,65,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,384] r41425 c41425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31060
  · exact u31061
  · exact u31062
  · exact u31063
  · exact u31064
  · exact u31065
  · exact u31066
  · exact u31067
  · exact u31068
  · exact u31069
  · exact u31070

def b41426 : PairBound 9 := { available := 470, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 69 41 470 502 470 470 470), lower := (rows 11 38 69 41 16 32 64 128 256), losses := [] }

theorem u41426 : Upper (D 6) (R 6) [10,36,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41427 : PairBound 9 := { available := 469, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 69 42 469 501 469 469 469), lower := (rows 11 38 69 42 16 32 64 128 256), losses := [] }

theorem u41427 : Upper (D 6) (R 6) [10,36,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41428 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 69 44 467 499 467 467 467), lower := (rows 11 38 69 44 16 32 64 128 256), losses := [] }

theorem u41428 : Upper (D 6) (R 6) [10,36,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41429 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41429 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41429 : Upper (D 6) (R 6) [10,36,65,48] 13 := by
  apply FastRouting.sound _ _ [10,36,65,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41429 c41429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31071
  · exact u31072
  · exact u31073
  · exact u31074
  · exact u31075
  · exact u31076
  · exact u31077
  · exact u31078
  · exact u31079
  · exact u31080
  · exact u31081

def b41430 : PairBound 9 := { available := 438, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 38 69 73 438 438 502 438 438), lower := (rows 11 38 69 73 16 32 64 128 256), losses := [] }

theorem u41430 : Upper (D 6) (R 6) [10,36,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41431 : PairBound 9 := { available := 437, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 38 69 74 437 437 501 437 437), lower := (rows 11 38 69 74 16 32 64 128 256), losses := [] }

theorem u41431 : Upper (D 6) (R 6) [10,36,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41432 : PairBound 9 := { available := 435, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 38 69 76 435 435 499 435 435), lower := (rows 11 38 69 76 16 32 64 128 256), losses := [] }

theorem u41432 : Upper (D 6) (R 6) [10,36,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41433 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41433 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41433 : Upper (D 6) (R 6) [10,36,65,80] 13 := by
  apply FastRouting.sound _ _ [10,36,65,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r41433 c41433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31082
  · exact u31083
  · exact u31084
  · exact u31085
  · exact u31086
  · exact u31087
  · exact u31088
  · exact u31089
  · exact u31090
  · exact u31091
  · exact u31092

def b41434 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 69 104 407 439 471 407 407), lower := (rows 11 38 69 104 16 32 64 128 256), losses := [] }

theorem u41434 : Upper (D 6) (R 6) [10,36,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41435 : Route 9 := (fun mask => (mask,id))

def c41435 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41435 : Upper (D 6) (R 6) [10,36,65,129] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41435 c41435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31093
  · exact u31094
  · exact u31095
  · exact u31096
  · exact u31097
  · exact u31098
  · exact u31099
  · exact u31100
  · exact u31101
  · exact u31102

def b41436 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 69 138 373 373 373 501 373), lower := (rows 11 38 69 138 16 32 64 128 256), losses := [] }

theorem u41436 : Upper (D 6) (R 6) [10,36,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41437 : Route 9 := (fun mask => (mask,id))

def c41437 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41437 : Upper (D 6) (R 6) [10,36,65,132] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41437 c41437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31103
  · exact u31104
  · exact u31105
  · exact u31106
  · exact u31107
  · exact u31108
  · exact u31109
  · exact u31110
  · exact u31111
  · exact u31112

def r41438 : Route 9 := (fun mask => (mask,id))

def c41438 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41438 : Upper (D 6) (R 6) [10,36,65,144] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41438 c41438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31113
  · exact u31114
  · exact u31115
  · exact u31116
  · exact u31117
  · exact u31118
  · exact u31119
  · exact u31120
  · exact u31121
  · exact u31122
  · exact u31123
  · exact u31124
  · exact u31125
  · exact u31126
  · exact u31127

def r41439 : Route 9 := (fun mask => (mask,id))

def c41439 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41439 : Upper (D 6) (R 6) [10,36,65,160] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41439 c41439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31128
  · exact u31129
  · exact u31130
  · exact u31131
  · exact u31132
  · exact u31133
  · exact u31134
  · exact u31135
  · exact u31136
  · exact u31137

def r41440 : Route 9 := (fun mask => (mask,id))

def c41440 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41440 : Upper (D 6) (R 6) [10,36,65,192] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41440 c41440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31138
  · exact u31139
  · exact u31140
  · exact u31141
  · exact u31142
  · exact u31143
  · exact u31144
  · exact u31145
  · exact u31146
  · exact u31147

def r41441 : Route 9 := (fun mask => (mask,id))

def c41441 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41441 : Upper (D 6) (R 6) [10,36,65,384] 13 := by
  apply FastRouting.sound _ _ [10,36,65,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41441 c41441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31148
  · exact u31149
  · exact u31150
  · exact u31151
  · exact u31152
  · exact u31153
  · exact u31154
  · exact u31155
  · exact u31156
  · exact u31157

def b41442 : PairBound 9 := { available := 497, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 70 13 497 497 497 497 497), lower := (rows 11 38 70 13 16 32 64 128 256), losses := [] }

theorem u41442 : Upper (D 6) (R 6) [10,36,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41443 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41443 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41443 : Upper (D 6) (R 6) [10,36,66,17] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r41443 c41443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31158
  · exact u31159
  · exact u31160
  · exact u31161
  · exact u31162
  · exact u31163
  · exact u31164
  · exact u31165
  · exact u31166
  · exact u31167
  · exact u31168

def r41444 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41444 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41444 : Upper (D 6) (R 6) [10,36,66,20] 13 := by
  apply FastRouting.sound _ _ [10,36,66,20] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r41444 c41444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31169
  · exact u31170
  · exact u31171
  · exact u31172
  · exact u31173
  · exact u31174
  · exact u31175

def b41445 : PairBound 9 := { available := 469, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 70 41 469 501 469 469 469), lower := (rows 11 38 70 41 16 32 64 128 256), losses := [] }

theorem u41445 : Upper (D 6) (R 6) [10,36,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41446 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 464, targets := 6 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 70 44 465 497 465 465 465), lower := (rows 11 38 70 44 16 32 64 128 256), losses := [] }

theorem u41446 : Upper (D 6) (R 6) [10,36,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41447 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41447 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41447 : Upper (D 6) (R 6) [10,36,66,48] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r41447 c41447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31176
  · exact u31177
  · exact u31178
  · exact u31179
  · exact u31180
  · exact u31181
  · exact u31182

def b41448 : PairBound 9 := { available := 437, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 70 73 437 437 501 437 437), lower := (rows 11 38 70 73 16 32 64 128 256), losses := [] }

theorem u41448 : Upper (D 6) (R 6) [10,36,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41449 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 70 76 433 433 497 433 433), lower := (rows 11 38 70 76 16 32 64 128 256), losses := [] }

theorem u41449 : Upper (D 6) (R 6) [10,36,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41450 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41450 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41450 : Upper (D 6) (R 6) [10,36,66,80] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r41450 c41450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31183
  · exact u31184
  · exact u31185
  · exact u31186
  · exact u31187
  · exact u31188
  · exact u31189

def b41451 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 70 104 405 437 469 405 405), lower := (rows 11 38 70 104 16 32 64 128 256), losses := [] }

theorem u41451 : Upper (D 6) (R 6) [10,36,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41452 : Route 9 := (fun mask => (mask,id))

def c41452 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41452 : Upper (D 6) (R 6) [10,36,66,129] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41452 c41452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31190
  · exact u31191
  · exact u31192
  · exact u31193
  · exact u31194
  · exact u31195
  · exact u31196
  · exact u31197
  · exact u31198
  · exact u31199

def r41453 : Route 9 := (fun mask => (mask,id))

def c41453 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41453 : Upper (D 6) (R 6) [10,36,66,132] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41453 c41453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31200
  · exact u31201
  · exact u31202
  · exact u31203
  · exact u31204
  · exact u31205

def r41454 : Route 9 := (fun mask => (mask,id))

def c41454 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41454 : Upper (D 6) (R 6) [10,36,66,144] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41454 c41454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31206
  · exact u31207
  · exact u31208
  · exact u31209
  · exact u31210
  · exact u31211
  · exact u31212
  · exact u31213
  · exact u31214
  · exact u31215

def r41455 : Route 9 := (fun mask => (mask,id))

def c41455 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41455 : Upper (D 6) (R 6) [10,36,66,160] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41455 c41455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31216
  · exact u31217
  · exact u31218
  · exact u31219
  · exact u31220
  · exact u31221

def r41456 : Route 9 := (fun mask => (mask,id))

def c41456 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41456 : Upper (D 6) (R 6) [10,36,66,192] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192] 13 (by decide) (choices 2) [5,33,36,257,260,288] r41456 c41456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31222
  · exact u31223
  · exact u31224
  · exact u31225
  · exact u31226
  · exact u31227

def r41457 : Route 9 := (fun mask => (mask,id))

def c41457 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41457 : Upper (D 6) (R 6) [10,36,66,384] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41457 c41457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31228
  · exact u31229
  · exact u31230
  · exact u31231
  · exact u31232
  · exact u31233

def b41458 : PairBound 9 := { available := 485, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 84 11 501 485 485 485 485), lower := (rows 11 38 84 11 16 32 64 128 256), losses := [] }

theorem u41458 : Upper (D 6) (R 6) [10,36,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41459 : PairBound 9 := { available := 483, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 84 13 499 483 483 483 483), lower := (rows 11 38 84 13 16 32 64 128 256), losses := [] }

theorem u41459 : Upper (D 6) (R 6) [10,36,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41459
end Delivery.IrregularNine14.P06
