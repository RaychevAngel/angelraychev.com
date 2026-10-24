import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0063

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11940 : Route 9 := (fun mask => (mask,id))

def c11940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11940 : Upper (D 8) (R 8) [66,257,40,192,160] 13 := by
  apply FastRouting.sound _ _ [66,257,40,192,160] 13 (by decide) (choices 1) [1,4,16] r11940 c11940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3820
  · exact u3821
  · exact u3822

def b11941 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 69 140 176 56 120 184 312), lower := (rows 67 259 69 140 176 32 64 128 256), losses := [] }

theorem u11941 : Upper (D 8) (R 8) [66,257,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11942 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 76 137 148 48 112 176 304), lower := (rows 67 259 76 137 148 32 64 128 256), losses := [] }

theorem u11942 : Upper (D 8) (R 8) [66,257,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11943 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 76 137 176 52 116 180 308), lower := (rows 67 259 76 137 176 32 64 128 256), losses := [] }

theorem u11943 : Upper (D 8) (R 8) [66,257,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11944 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 76 140 176 49 113 177 305), lower := (rows 67 259 76 140 176 32 64 128 256), losses := [] }

theorem u11944 : Upper (D 8) (R 8) [66,257,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11945 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 76 152 145 36 100 164 292), lower := (rows 67 259 76 152 145 32 64 128 256), losses := [] }

theorem u11945 : Upper (D 8) (R 8) [66,257,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11946 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 76 152 148 33 97 161 289), lower := (rows 67 259 76 152 148 32 64 128 256), losses := [] }

theorem u11946 : Upper (D 8) (R 8) [66,257,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11947 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 76 152 176 37 101 165 293), lower := (rows 67 259 76 152 176 32 64 128 256), losses := [] }

theorem u11947 : Upper (D 8) (R 8) [66,257,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11948 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 76 168 145 52 116 180 308), lower := (rows 67 259 76 168 145 32 64 128 256), losses := [] }

theorem u11948 : Upper (D 8) (R 8) [66,257,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11949 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 76 168 148 49 113 177 305), lower := (rows 67 259 76 168 148 32 64 128 256), losses := [] }

theorem u11949 : Upper (D 8) (R 8) [66,257,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11950 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 259 76 168 176 53 117 181 309), lower := (rows 67 259 76 168 176 32 64 128 256), losses := [] }

theorem u11950 : Upper (D 8) (R 8) [66,257,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11951 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 100 137 148 56 120 184 312), lower := (rows 67 259 100 137 148 32 64 128 256), losses := [] }

theorem u11951 : Upper (D 8) (R 8) [66,257,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11952 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 100 137 152 52 116 180 308), lower := (rows 67 259 100 137 152 32 64 128 256), losses := [] }

theorem u11952 : Upper (D 8) (R 8) [66,257,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11953 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 100 137 176 60 124 188 316), lower := (rows 67 259 100 137 176 32 64 128 256), losses := [] }

theorem u11953 : Upper (D 8) (R 8) [66,257,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11954 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 259 100 140 152 49 113 177 305), lower := (rows 67 259 100 140 152 32 64 128 256), losses := [] }

theorem u11954 : Upper (D 8) (R 8) [66,257,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11955 : Route 9 := (fun mask => (mask,id))

def c11955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11955 : Upper (D 8) (R 8) [66,257,96,132,160] 13 := by
  apply FastRouting.sound _ _ [66,257,96,132,160] 13 (by decide) (choices 1) [1,8,16] r11955 c11955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3823
  · exact u3824
  · exact u3825

def b11956 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 100 152 152 37 101 165 293), lower := (rows 67 259 100 152 152 32 64 128 256), losses := [] }

theorem u11956 : Upper (D 8) (R 8) [66,257,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11957 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 100 152 176 45 109 173 301), lower := (rows 67 259 100 152 176 32 64 128 256), losses := [] }

theorem u11957 : Upper (D 8) (R 8) [66,257,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11958 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 259 100 168 176 61 93 157 285), lower := (rows 67 259 100 168 176 32 64 128 256), losses := [] }

theorem u11958 : Upper (D 8) (R 8) [66,257,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11959 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 262 13 56 49 224 224 224 480), lower := (rows 67 262 13 56 49 32 64 128 256), losses := [] }

theorem u11959 : Upper (D 8) (R 8) [66,260,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11960 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 56 81 160 224 160 416), lower := (rows 67 262 13 56 81 32 64 128 256), losses := [] }

theorem u11960 : Upper (D 8) (R 8) [66,260,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11961 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 56 112 161 225 161 417), lower := (rows 67 262 13 56 112 32 64 128 256), losses := [] }

theorem u11961 : Upper (D 8) (R 8) [66,260,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11962 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 13 56 145 224 224 224 480), lower := (rows 67 262 13 56 145 32 64 128 256), losses := [] }

theorem u11962 : Upper (D 8) (R 8) [66,260,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11963 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 56 176 225 225 225 481), lower := (rows 67 262 13 56 176 32 64 128 256), losses := [] }

theorem u11963 : Upper (D 8) (R 8) [66,260,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11964 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 56 208 161 225 161 417), lower := (rows 67 262 13 56 208 32 64 128 256), losses := [] }

theorem u11964 : Upper (D 8) (R 8) [66,260,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11965 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 13 152 49 224 224 224 480), lower := (rows 67 262 13 152 49 32 64 128 256), losses := [] }

theorem u11965 : Upper (D 8) (R 8) [66,260,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11966 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 152 81 160 224 160 416), lower := (rows 67 262 13 152 81 32 64 128 256), losses := [] }

theorem u11966 : Upper (D 8) (R 8) [66,260,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11967 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 152 112 161 225 161 417), lower := (rows 67 262 13 152 112 32 64 128 256), losses := [] }

theorem u11967 : Upper (D 8) (R 8) [66,260,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11968 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 13 152 145 96 96 224 352), lower := (rows 67 262 13 152 145 32 64 128 256), losses := [] }

theorem u11968 : Upper (D 8) (R 8) [66,260,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11969 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 13 152 176 97 97 225 353), lower := (rows 67 262 13 152 176 32 64 128 256), losses := [] }

theorem u11969 : Upper (D 8) (R 8) [66,260,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11970 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 13 152 208 33 97 161 289), lower := (rows 67 262 13 152 208 32 64 128 256), losses := [] }

theorem u11970 : Upper (D 8) (R 8) [66,260,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11971 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 168 49 240 240 240 496), lower := (rows 67 262 13 168 49 32 64 128 256), losses := [] }

theorem u11971 : Upper (D 8) (R 8) [66,260,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11972 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 13 168 81 176 240 176 432), lower := (rows 67 262 13 168 81 32 64 128 256), losses := [] }

theorem u11972 : Upper (D 8) (R 8) [66,260,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11973 : Route 9 := (fun mask => (mask,id))

def c11973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11973 : Upper (D 8) (R 8) [66,260,9,160,96] 13 := by
  apply FastRouting.sound _ _ [66,260,9,160,96] 13 (by decide) (choices 1) [1,16,128] r11973 c11973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3826
  · exact u3827
  · exact u3828

def b11974 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 168 145 112 112 240 368), lower := (rows 67 262 13 168 145 32 64 128 256), losses := [] }

theorem u11974 : Upper (D 8) (R 8) [66,260,9,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11975 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 13 168 176 113 113 241 369), lower := (rows 67 262 13 168 176 32 64 128 256), losses := [] }

theorem u11975 : Upper (D 8) (R 8) [66,260,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11976 : Route 9 := (fun mask => (mask,id))

def c11976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11976 : Upper (D 8) (R 8) [66,260,9,160,192] 13 := by
  apply FastRouting.sound _ _ [66,260,9,160,192] 13 (by decide) (choices 1) [1,16] r11976 c11976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3829
  · exact u3830

def b11977 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 262 28 41 49 224 224 224 480), lower := (rows 67 262 28 41 49 32 64 128 256), losses := [] }

theorem u11977 : Upper (D 8) (R 8) [66,260,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11978 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 28 41 81 160 224 160 416), lower := (rows 67 262 28 41 81 32 64 128 256), losses := [] }

theorem u11978 : Upper (D 8) (R 8) [66,260,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11979 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 28 41 112 161 225 161 417), lower := (rows 67 262 28 41 112 32 64 128 256), losses := [] }

theorem u11979 : Upper (D 8) (R 8) [66,260,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11980 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 28 41 145 224 224 224 480), lower := (rows 67 262 28 41 145 32 64 128 256), losses := [] }

theorem u11980 : Upper (D 8) (R 8) [66,260,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11981 : Route 9 := (fun mask => (mask,id))

def c11981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11981 : Upper (D 8) (R 8) [66,260,24,33,160] 13 := by
  apply FastRouting.sound _ _ [66,260,24,33,160] 13 (by decide) (choices 1) [1,64,128] r11981 c11981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3831
  · exact u3832
  · exact u3833

def b11982 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 28 41 208 161 225 161 417), lower := (rows 67 262 28 41 208 32 64 128 256), losses := [] }

theorem u11982 : Upper (D 8) (R 8) [66,260,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11983 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 28 73 145 160 224 160 416), lower := (rows 67 262 28 73 145 32 64 128 256), losses := [] }

theorem u11983 : Upper (D 8) (R 8) [66,260,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11984 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 28 73 176 161 225 161 417), lower := (rows 67 262 28 73 176 32 64 128 256), losses := [] }

theorem u11984 : Upper (D 8) (R 8) [66,260,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11985 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 28 104 145 161 225 161 417), lower := (rows 67 262 28 104 145 32 64 128 256), losses := [] }

theorem u11985 : Upper (D 8) (R 8) [66,260,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11986 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 28 104 176 161 225 161 417), lower := (rows 67 262 28 104 176 32 64 128 256), losses := [] }

theorem u11986 : Upper (D 8) (R 8) [66,260,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11987 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 28 137 145 96 96 224 352), lower := (rows 67 262 28 137 145 32 64 128 256), losses := [] }

theorem u11987 : Upper (D 8) (R 8) [66,260,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11988 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 28 137 176 97 97 225 353), lower := (rows 67 262 28 137 176 32 64 128 256), losses := [] }

theorem u11988 : Upper (D 8) (R 8) [66,260,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11989 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 28 137 208 33 97 161 289), lower := (rows 67 262 28 137 208 32 64 128 256), losses := [] }

theorem u11989 : Upper (D 8) (R 8) [66,260,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11990 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 28 168 176 97 97 225 353), lower := (rows 67 262 28 168 176 32 64 128 256), losses := [] }

theorem u11990 : Upper (D 8) (R 8) [66,260,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11991 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 28 168 208 33 97 161 289), lower := (rows 67 262 28 168 208 32 64 128 256), losses := [] }

theorem u11991 : Upper (D 8) (R 8) [66,260,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11992 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 25 56 224 224 224 480), lower := (rows 67 262 37 25 56 32 64 128 256), losses := [] }

theorem u11992 : Upper (D 8) (R 8) [66,260,33,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11993 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 37 25 88 160 224 160 416), lower := (rows 67 262 37 25 88 32 64 128 256), losses := [] }

theorem u11993 : Upper (D 8) (R 8) [66,260,33,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11994 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 25 112 168 232 168 424), lower := (rows 67 262 37 25 112 32 64 128 256), losses := [] }

theorem u11994 : Upper (D 8) (R 8) [66,260,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11995 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 25 152 224 224 224 480), lower := (rows 67 262 37 25 152 32 64 128 256), losses := [] }

theorem u11995 : Upper (D 8) (R 8) [66,260,33,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11996 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 25 176 232 232 232 488), lower := (rows 67 262 37 25 176 32 64 128 256), losses := [] }

theorem u11996 : Upper (D 8) (R 8) [66,260,33,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11997 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 25 208 168 232 168 424), lower := (rows 67 262 37 25 208 32 64 128 256), losses := [] }

theorem u11997 : Upper (D 8) (R 8) [66,260,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11998 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 56 240 208 208 464), lower := (rows 67 262 37 41 56 32 64 128 256), losses := [] }

theorem u11998 : Upper (D 8) (R 8) [66,260,33,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11999 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 88 176 240 176 432), lower := (rows 67 262 37 41 88 32 64 128 256), losses := [] }

theorem u11999 : Upper (D 8) (R 8) [66,260,33,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11999
end Delivery.IrregularNine14.P08
