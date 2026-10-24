import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0012
import IrregularNine14P05C0013

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 273 36 74 138 266), lower := (rows 7 67 164 56 273 36 64 128 256), losses := [] }

theorem u3000 : Upper (D 5) (R 5) [6,65,160,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 273 40 78 142 270), lower := (rows 7 67 164 56 273 40 64 128 256), losses := [] }

theorem u3001 : Upper (D 5) (R 5) [6,65,160,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 274 33 76 140 268), lower := (rows 7 67 164 56 274 33 64 128 256), losses := [] }

theorem u3002 : Upper (D 5) (R 5) [6,65,160,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 274 36 73 137 265), lower := (rows 7 67 164 56 274 36 64 128 256), losses := [] }

theorem u3003 : Upper (D 5) (R 5) [6,65,160,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 274 40 77 141 269), lower := (rows 7 67 164 56 274 40 64 128 256), losses := [] }

theorem u3004 : Upper (D 5) (R 5) [6,65,160,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 10, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 56 276 33 74 138 266), lower := (rows 7 67 164 56 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 65 129 257), good := (rows 478 466 188 60 284 508 64 128 256) }] }

theorem u3005 : Upper (D 5) (R 5) [6,65,160,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3006 : Route 9 := (fun mask => (mask,id))

def c3006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3006 : Upper (D 5) (R 5) [6,65,160,48,260,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,260,2] 13 (by decide) (choices 1) [1,8] r3006 c3006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u773
  · exact u774

def b3007 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 276 40 75 139 267), lower := (rows 7 67 164 56 276 40 64 128 256), losses := [] }

theorem u3007 : Upper (D 5) (R 5) [6,65,160,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3008 : PairBound 9 := { available := 14, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 56 280 33 78 142 270), lower := (rows 7 67 164 56 280 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 65 129 257), good := (rows 478 466 188 60 280 508 64 128 256) }] }

theorem u3008 : Upper (D 5) (R 5) [6,65,160,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3008
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3009 : Route 9 := (fun mask => (mask,id))

def c3009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3009 : Upper (D 5) (R 5) [6,65,160,48,264,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,264,2] 13 (by decide) (choices 1) [1,4,8] r3009 c3009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u775
  · exact u776
  · exact u777

def b3010 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 280 36 75 139 267), lower := (rows 7 67 164 56 280 36 64 128 256), losses := [] }

theorem u3010 : Upper (D 5) (R 5) [6,65,160,48,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 280 40 71 135 263), lower := (rows 7 67 164 56 280 40 64 128 256), losses := [] }

theorem u3011 : Upper (D 5) (R 5) [6,65,160,48,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 56, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 164 265 28 34 120 184 312), lower := (rows 7 67 164 265 28 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 98 164 508 476 34 64 128 256) }] }

theorem u3012 : Upper (D 5) (R 5) [6,65,160,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3013 : Route 9 := (fun mask => (mask,id))

def c3013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3013 : Upper (D 5) (R 5) [6,65,160,257,12,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,12,8] 13 (by decide) (choices 1) [2,16,32] r3013 c3013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u778
  · exact u779
  · exact u780

def r3014 : Route 9 := (fun mask => (mask,id))

def c3014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3014 : Upper (D 5) (R 5) [6,65,160,257,12,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,12,16] 13 (by decide) (choices 1) [2,8,32] r3014 c3014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u781
  · exact u782
  · exact u783

def b3015 : PairBound 9 := { available := 24, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 265 50 36 88 152 280), lower := (rows 7 67 164 265 50 36 64 128 256), losses := [] }

theorem u3015 : Upper (D 5) (R 5) [6,65,160,257,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3016 : Route 9 := (fun mask => (mask,id))

def c3016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3016 : Upper (D 5) (R 5) [6,65,160,257,34,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,34,8] 13 (by decide) (choices 1) [4,8,16] r3016 c3016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u784
  · exact u785
  · exact u786

def b3017 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 164 265 50 48 76 140 268), lower := (rows 7 67 164 265 50 48 64 128 256), losses := [] }

theorem u3017 : Upper (D 5) (R 5) [6,65,160,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 265 56 34 92 156 284), lower := (rows 7 67 164 265 56 34 64 128 256), losses := [] }

theorem u3018 : Upper (D 5) (R 5) [6,65,160,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 26, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 265 56 36 90 154 282), lower := (rows 7 67 164 265 56 36 64 128 256), losses := [] }

theorem u3019 : Upper (D 5) (R 5) [6,65,160,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3019
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 265 56 40 86 150 278), lower := (rows 7 67 164 265 56 40 64 128 256), losses := [] }

theorem u3020 : Upper (D 5) (R 5) [6,65,160,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 265 56 48 78 142 270), lower := (rows 7 67 164 265 56 48 64 128 256), losses := [] }

theorem u3021 : Upper (D 5) (R 5) [6,65,160,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 56, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 164 266 28 33 120 184 312), lower := (rows 7 67 164 266 28 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 97 164 508 476 33 64 128 256) }] }

theorem u3022 : Upper (D 5) (R 5) [6,65,160,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3023 : Route 9 := (fun mask => (mask,id))

def c3023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3023 : Upper (D 5) (R 5) [6,65,160,258,12,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,12,8] 13 (by decide) (choices 1) [1,16,32] r3023 c3023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u787
  · exact u788
  · exact u789

def r3024 : Route 9 := (fun mask => (mask,id))

def c3024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3024 : Upper (D 5) (R 5) [6,65,160,258,12,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,12,16] 13 (by decide) (choices 1) [1,8,32] r3024 c3024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u790
  · exact u791
  · exact u792

def b3025 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 67 164 266 49 36 88 152 280), lower := (rows 7 67 164 266 49 36 64 128 256), losses := [] }

theorem u3025 : Upper (D 5) (R 5) [6,65,160,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3026 : Route 9 := (fun mask => (mask,id))

def c3026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3026 : Upper (D 5) (R 5) [6,65,160,258,33,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,33,8] 13 (by decide) (choices 1) [4,8,16] r3026 c3026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u793
  · exact u794
  · exact u795

def b3027 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 164 266 49 48 76 140 268), lower := (rows 7 67 164 266 49 48 64 128 256), losses := [] }

theorem u3027 : Upper (D 5) (R 5) [6,65,160,258,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3027
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 266 56 33 92 156 284), lower := (rows 7 67 164 266 56 33 64 128 256), losses := [] }

theorem u3028 : Upper (D 5) (R 5) [6,65,160,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 266 56 36 89 153 281), lower := (rows 7 67 164 266 56 36 64 128 256), losses := [] }

theorem u3029 : Upper (D 5) (R 5) [6,65,160,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3029
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 266 56 40 85 149 277), lower := (rows 7 67 164 266 56 40 64 128 256), losses := [] }

theorem u3030 : Upper (D 5) (R 5) [6,65,160,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 266 56 48 77 141 269), lower := (rows 7 67 164 266 56 48 64 128 256), losses := [] }

theorem u3031 : Upper (D 5) (R 5) [6,65,160,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 67 164 268 25 34 120 184 312), lower := (rows 7 67 164 268 25 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 98 164 268 508 34 64 128 256) }] }

theorem u3032 : Upper (D 5) (R 5) [6,65,160,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3032
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3033 : Route 9 := (fun mask => (mask,id))

def c3033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3033 : Upper (D 5) (R 5) [6,65,160,260,9,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,9,8] 13 (by decide) (choices 1) [2,16,32] r3033 c3033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u796
  · exact u797
  · exact u798

def b3034 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 164 268 25 48 106 170 298), lower := (rows 7 67 164 268 25 48 64 128 256), losses := [] }

theorem u3034 : Upper (D 5) (R 5) [6,65,160,260,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 56, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 268 26 33 120 184 312), lower := (rows 7 67 164 268 26 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 17 32 96 160 288), good := (rows 30 82 492 268 26 508 64 128 256) }] }

theorem u3035 : Upper (D 5) (R 5) [6,65,160,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3036 : Route 9 := (fun mask => (mask,id))

def c3036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3036 : Upper (D 5) (R 5) [6,65,160,260,10,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,10,8] 13 (by decide) (choices 1) [1,16,32] r3036 c3036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u799
  · exact u800
  · exact u801

def r3037 : Route 9 := (fun mask => (mask,id))

def c3037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3037 : Upper (D 5) (R 5) [6,65,160,260,10,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,10,16] 13 (by decide) (choices 1) [1,8,32] r3037 c3037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u802
  · exact u803
  · exact u804

def b3038 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 49 34 88 152 280), lower := (rows 7 67 164 268 49 34 64 128 256), losses := [] }

theorem u3038 : Upper (D 5) (R 5) [6,65,160,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3039 : Route 9 := (fun mask => (mask,id))

def c3039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3039 : Upper (D 5) (R 5) [6,65,160,260,33,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,33,8] 13 (by decide) (choices 1) [2,8,16] r3039 c3039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u805
  · exact u806
  · exact u807

def b3040 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 164 268 49 48 74 138 266), lower := (rows 7 67 164 268 49 48 64 128 256), losses := [] }

theorem u3040 : Upper (D 5) (R 5) [6,65,160,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 50 33 88 152 280), lower := (rows 7 67 164 268 50 33 64 128 256), losses := [] }

theorem u3041 : Upper (D 5) (R 5) [6,65,160,260,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3041
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3042 : Route 9 := (fun mask => (mask,id))

def c3042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3042 : Upper (D 5) (R 5) [6,65,160,260,34,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,34,8] 13 (by decide) (choices 1) [1,8,16] r3042 c3042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u808
  · exact u809
  · exact u810

def b3043 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 164 268 50 48 73 137 265), lower := (rows 7 67 164 268 50 48 64 128 256), losses := [] }

theorem u3043 : Upper (D 5) (R 5) [6,65,160,260,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 26, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 268 56 33 90 154 282), lower := (rows 7 67 164 268 56 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 52 32 65 129 257), good := (rows 478 458 188 284 60 508 64 128 256) }] }

theorem u3044 : Upper (D 5) (R 5) [6,65,160,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3045 : Route 9 := (fun mask => (mask,id))

def c3045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3045 : Upper (D 5) (R 5) [6,65,160,260,40,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,40,2] 13 (by decide) (choices 1) [1,8,16] r3045 c3045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u811
  · exact u812
  · exact u813

def b3046 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 268 56 40 83 147 275), lower := (rows 7 67 164 268 56 40 64 128 256), losses := [] }

theorem u3046 : Upper (D 5) (R 5) [6,65,160,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3046
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 268 56 48 75 139 267), lower := (rows 7 67 164 268 56 48 64 128 256), losses := [] }

theorem u3047 : Upper (D 5) (R 5) [6,65,160,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3048 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 280 25 34 108 172 300), lower := (rows 7 67 164 280 25 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 98 164 476 508 34 64 128 256) }] }

theorem u3048 : Upper (D 5) (R 5) [6,65,160,272,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 42, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 25 36 106 170 298), lower := (rows 7 67 164 280 25 36 64 128 256), losses := [] }

theorem u3049 : Upper (D 5) (R 5) [6,65,160,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3050 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 25 40 102 166 294), lower := (rows 7 67 164 280 25 40 64 128 256), losses := [] }

theorem u3050 : Upper (D 5) (R 5) [6,65,160,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 280 26 33 108 172 300), lower := (rows 7 67 164 280 26 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 19 32 100 164 292), good := (rows 478 90 492 280 26 508 64 128 256) }] }

theorem u3051 : Upper (D 5) (R 5) [6,65,160,272,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 41, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 26 36 105 169 297), lower := (rows 7 67 164 280 26 36 64 128 256), losses := [] }

theorem u3052 : Upper (D 5) (R 5) [6,65,160,272,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 26 40 101 165 293), lower := (rows 7 67 164 280 26 40 64 128 256), losses := [] }

theorem u3053 : Upper (D 5) (R 5) [6,65,160,272,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3054 : Route 9 := (fun mask => (mask,id))

def c3054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3054 : Upper (D 5) (R 5) [6,65,160,272,12,1] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,12,1] 13 (by decide) (choices 1) [2,8,32] r3054 c3054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u814
  · exact u815
  · exact u816

def r3055 : Route 9 := (fun mask => (mask,id))

def c3055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3055 : Upper (D 5) (R 5) [6,65,160,272,12,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,12,2] 13 (by decide) (choices 1) [1,8,32] r3055 c3055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u817
  · exact u818
  · exact u819

def b3056 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 28 40 99 163 291), lower := (rows 7 67 164 280 28 40 64 128 256), losses := [] }

theorem u3056 : Upper (D 5) (R 5) [6,65,160,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3056
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3057 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 49 34 76 140 268), lower := (rows 7 67 164 280 49 34 64 128 256), losses := [] }

theorem u3057 : Upper (D 5) (R 5) [6,65,160,272,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 67 164 280 49 36 74 138 266), lower := (rows 7 67 164 280 49 36 64 128 256), losses := [] }

theorem u3058 : Upper (D 5) (R 5) [6,65,160,272,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3059 : Route 9 := (fun mask => (mask,id))

def c3059 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3059 : Upper (D 5) (R 5) [6,65,160,272,33,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,33,8] 13 (by decide) (choices 1) [2,4,8] r3059 c3059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u820
  · exact u821
  · exact u822

#print axioms u3059
end Delivery.IrregularNine14.P05
