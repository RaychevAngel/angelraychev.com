import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0064
import IrregularNine14P08C0065

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12060 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 56 88 161 225 161 417), lower := (rows 67 262 133 56 88 32 64 128 256), losses := [] }

theorem u12060 : Upper (D 8) (R 8) [66,260,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12061 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 56 112 169 233 169 425), lower := (rows 67 262 133 56 112 32 64 128 256), losses := [] }

theorem u12061 : Upper (D 8) (R 8) [66,260,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12062 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 262 133 56 145 104 104 232 360), lower := (rows 67 262 133 56 145 32 64 128 256), losses := [] }

theorem u12062 : Upper (D 8) (R 8) [66,260,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12063 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 133 56 152 97 97 225 353), lower := (rows 67 262 133 56 152 32 64 128 256), losses := [] }

theorem u12063 : Upper (D 8) (R 8) [66,260,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12064 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 56 176 105 105 233 361), lower := (rows 67 262 133 56 176 32 64 128 256), losses := [] }

theorem u12064 : Upper (D 8) (R 8) [66,260,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12065 : Route 9 := (fun mask => (mask,id))

def c12065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12065 : Upper (D 8) (R 8) [66,260,129,48,192] 13 := by
  apply FastRouting.sound _ _ [66,260,129,48,192] 13 (by decide) (choices 1) [1,8] r12065 c12065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3872
  · exact u3873

def b12066 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 73 152 48 112 176 304), lower := (rows 67 262 133 73 152 32 64 128 256), losses := [] }

theorem u12066 : Upper (D 8) (R 8) [66,260,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12067 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 73 176 56 120 184 312), lower := (rows 67 262 133 73 176 32 64 128 256), losses := [] }

theorem u12067 : Upper (D 8) (R 8) [66,260,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12068 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 262 133 88 145 40 104 168 296), lower := (rows 67 262 133 88 145 32 64 128 256), losses := [] }

theorem u12068 : Upper (D 8) (R 8) [66,260,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12069 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 88 152 33 97 161 289), lower := (rows 67 262 133 88 152 32 64 128 256), losses := [] }

theorem u12069 : Upper (D 8) (R 8) [66,260,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12070 : Route 9 := (fun mask => (mask,id))

def c12070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12070 : Upper (D 8) (R 8) [66,260,129,80,160] 13 := by
  apply FastRouting.sound _ _ [66,260,129,80,160] 13 (by decide) (choices 1) [1,8] r12070 c12070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3874
  · exact u3875

def b12071 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 262 133 104 145 56 120 184 312), lower := (rows 67 262 133 104 145 32 64 128 256), losses := [] }

theorem u12071 : Upper (D 8) (R 8) [66,260,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12072 : Route 9 := (fun mask => (mask,id))

def c12072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12072 : Upper (D 8) (R 8) [66,260,129,96,136] 13 := by
  apply FastRouting.sound _ _ [66,260,129,96,136] 13 (by decide) (choices 1) [1,16] r12072 c12072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3876
  · exact u3877

def r12073 : Route 9 := (fun mask => (mask,id))

def c12073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12073 : Upper (D 8) (R 8) [66,260,129,96,160] 13 := by
  apply FastRouting.sound _ _ [66,260,129,96,160] 13 (by decide) (choices 1) [1,8,16] r12073 c12073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3878
  · exact u3879
  · exact u3880

def b12074 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 140 25 49 224 224 224 480), lower := (rows 67 262 140 25 49 32 64 128 256), losses := [] }

theorem u12074 : Upper (D 8) (R 8) [66,260,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12075 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 140 25 81 160 224 160 416), lower := (rows 67 262 140 25 81 32 64 128 256), losses := [] }

theorem u12075 : Upper (D 8) (R 8) [66,260,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12076 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 140 25 112 161 225 161 417), lower := (rows 67 262 140 25 112 32 64 128 256), losses := [] }

theorem u12076 : Upper (D 8) (R 8) [66,260,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12077 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 262 140 25 145 96 96 224 352), lower := (rows 67 262 140 25 145 32 64 128 256), losses := [] }

theorem u12077 : Upper (D 8) (R 8) [66,260,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12078 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 140 25 176 97 97 225 353), lower := (rows 67 262 140 25 176 32 64 128 256), losses := [] }

theorem u12078 : Upper (D 8) (R 8) [66,260,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12079 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 140 25 208 33 97 161 289), lower := (rows 67 262 140 25 208 32 64 128 256), losses := [] }

theorem u12079 : Upper (D 8) (R 8) [66,260,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12080 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 140 41 49 240 240 240 496), lower := (rows 67 262 140 41 49 32 64 128 256), losses := [] }

theorem u12080 : Upper (D 8) (R 8) [66,260,136,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12081 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 140 41 81 176 240 176 432), lower := (rows 67 262 140 41 81 32 64 128 256), losses := [] }

theorem u12081 : Upper (D 8) (R 8) [66,260,136,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12082 : Route 9 := (fun mask => (mask,id))

def c12082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12082 : Upper (D 8) (R 8) [66,260,136,33,96] 13 := by
  apply FastRouting.sound _ _ [66,260,136,33,96] 13 (by decide) (choices 1) [1,16,128] r12082 c12082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3881
  · exact u3882
  · exact u3883

def b12083 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 140 41 145 112 112 240 368), lower := (rows 67 262 140 41 145 32 64 128 256), losses := [] }

theorem u12083 : Upper (D 8) (R 8) [66,260,136,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12084 : Route 9 := (fun mask => (mask,id))

def c12084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12084 : Upper (D 8) (R 8) [66,260,136,33,160] 13 := by
  apply FastRouting.sound _ _ [66,260,136,33,160] 13 (by decide) (choices 1) [1,16,64] r12084 c12084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3884
  · exact u3885
  · exact u3886

def r12085 : Route 9 := (fun mask => (mask,id))

def c12085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12085 : Upper (D 8) (R 8) [66,260,136,33,192] 13 := by
  apply FastRouting.sound _ _ [66,260,136,33,192] 13 (by decide) (choices 1) [1,16] r12085 c12085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3887
  · exact u3888

def b12086 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 140 56 49 225 225 225 481), lower := (rows 67 262 140 56 49 32 64 128 256), losses := [] }

theorem u12086 : Upper (D 8) (R 8) [66,260,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12087 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 140 56 81 161 225 161 417), lower := (rows 67 262 140 56 81 32 64 128 256), losses := [] }

theorem u12087 : Upper (D 8) (R 8) [66,260,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12088 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 140 56 112 161 225 161 417), lower := (rows 67 262 140 56 112 32 64 128 256), losses := [] }

theorem u12088 : Upper (D 8) (R 8) [66,260,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12089 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 140 56 145 97 97 225 353), lower := (rows 67 262 140 56 145 32 64 128 256), losses := [] }

theorem u12089 : Upper (D 8) (R 8) [66,260,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12090 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 140 56 176 97 97 225 353), lower := (rows 67 262 140 56 176 32 64 128 256), losses := [] }

theorem u12090 : Upper (D 8) (R 8) [66,260,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12091 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 140 56 208 33 97 161 289), lower := (rows 67 262 140 56 208 32 64 128 256), losses := [] }

theorem u12091 : Upper (D 8) (R 8) [66,260,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12092 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 164 25 25 224 224 224 480), lower := (rows 67 262 164 25 25 32 64 128 256), losses := [] }

theorem u12092 : Upper (D 8) (R 8) [66,260,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12093 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 164 25 49 232 232 232 488), lower := (rows 67 262 164 25 49 32 64 128 256), losses := [] }

theorem u12093 : Upper (D 8) (R 8) [66,260,160,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12094 : Route 9 := (fun mask => (mask,id))

def c12094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12094 : Upper (D 8) (R 8) [66,260,160,17,40] 13 := by
  apply FastRouting.sound _ _ [66,260,160,17,40] 13 (by decide) (choices 1) [1,64,128] r12094 c12094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3889
  · exact u3890
  · exact u3891

def b12095 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 164 25 81 168 232 168 424), lower := (rows 67 262 164 25 81 32 64 128 256), losses := [] }

theorem u12095 : Upper (D 8) (R 8) [66,260,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12096 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 164 25 88 161 225 161 417), lower := (rows 67 262 164 25 88 32 64 128 256), losses := [] }

theorem u12096 : Upper (D 8) (R 8) [66,260,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12097 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 25 112 169 233 169 425), lower := (rows 67 262 164 25 112 32 64 128 256), losses := [] }

theorem u12097 : Upper (D 8) (R 8) [66,260,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12098 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 25 145 104 104 232 360), lower := (rows 67 262 164 25 145 32 64 128 256), losses := [] }

theorem u12098 : Upper (D 8) (R 8) [66,260,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12099 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 164 25 152 97 97 225 353), lower := (rows 67 262 164 25 152 32 64 128 256), losses := [] }

theorem u12099 : Upper (D 8) (R 8) [66,260,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12100 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 164 25 176 105 105 233 361), lower := (rows 67 262 164 25 176 32 64 128 256), losses := [] }

theorem u12100 : Upper (D 8) (R 8) [66,260,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12101 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 25 208 41 105 169 297), lower := (rows 67 262 164 25 208 32 64 128 256), losses := [] }

theorem u12101 : Upper (D 8) (R 8) [66,260,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12102 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 164 41 49 248 216 216 472), lower := (rows 67 262 164 41 49 32 64 128 256), losses := [] }

theorem u12102 : Upper (D 8) (R 8) [66,260,160,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12103 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 164 41 56 241 209 209 465), lower := (rows 67 262 164 41 56 32 64 128 256), losses := [] }

theorem u12103 : Upper (D 8) (R 8) [66,260,160,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12104 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 41 81 184 248 184 440), lower := (rows 67 262 164 41 81 32 64 128 256), losses := [] }

theorem u12104 : Upper (D 8) (R 8) [66,260,160,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12105 : Route 9 := (fun mask => (mask,id))

def c12105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12105 : Upper (D 8) (R 8) [66,260,160,33,72] 13 := by
  apply FastRouting.sound _ _ [66,260,160,33,72] 13 (by decide) (choices 1) [1,16,128] r12105 c12105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3892
  · exact u3893
  · exact u3894

def r12106 : Route 9 := (fun mask => (mask,id))

def c12106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12106 : Upper (D 8) (R 8) [66,260,160,33,96] 13 := by
  apply FastRouting.sound _ _ [66,260,160,33,96] 13 (by decide) (choices 1) [1,8,16,128] r12106 c12106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3895
  · exact u3896
  · exact u3897
  · exact u3898

def b12107 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 41 145 120 120 248 376), lower := (rows 67 262 164 41 145 32 64 128 256), losses := [] }

theorem u12107 : Upper (D 8) (R 8) [66,260,160,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12108 : Route 9 := (fun mask => (mask,id))

def c12108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12108 : Upper (D 8) (R 8) [66,260,160,33,136] 13 := by
  apply FastRouting.sound _ _ [66,260,160,33,136] 13 (by decide) (choices 1) [1,16,64] r12108 c12108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3899
  · exact u3900
  · exact u3901

def b12109 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 164 41 176 121 89 217 345), lower := (rows 67 262 164 41 176 32 64 128 256), losses := [] }

theorem u12109 : Upper (D 8) (R 8) [66,260,160,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12110 : Route 9 := (fun mask => (mask,id))

def c12110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12110 : Upper (D 8) (R 8) [66,260,160,33,192] 13 := by
  apply FastRouting.sound _ _ [66,260,160,33,192] 13 (by decide) (choices 1) [1,8,16] r12110 c12110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3902
  · exact u3903
  · exact u3904

def b12111 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 164 56 56 225 193 193 449), lower := (rows 67 262 164 56 56 32 64 128 256), losses := [] }

theorem u12111 : Upper (D 8) (R 8) [66,260,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12112 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 56 81 169 233 169 425), lower := (rows 67 262 164 56 81 32 64 128 256), losses := [] }

theorem u12112 : Upper (D 8) (R 8) [66,260,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12113 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 56 88 161 225 161 417), lower := (rows 67 262 164 56 88 32 64 128 256), losses := [] }

theorem u12113 : Upper (D 8) (R 8) [66,260,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12114 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 164 56 112 169 201 137 393), lower := (rows 67 262 164 56 112 32 64 128 256), losses := [] }

theorem u12114 : Upper (D 8) (R 8) [66,260,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12115 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 56 145 105 105 233 361), lower := (rows 67 262 164 56 145 32 64 128 256), losses := [] }

theorem u12115 : Upper (D 8) (R 8) [66,260,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12116 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 164 56 152 97 97 225 353), lower := (rows 67 262 164 56 152 32 64 128 256), losses := [] }

theorem u12116 : Upper (D 8) (R 8) [66,260,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12117 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 164 56 176 105 73 201 329), lower := (rows 67 262 164 56 176 32 64 128 256), losses := [] }

theorem u12117 : Upper (D 8) (R 8) [66,260,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12118 : Route 9 := (fun mask => (mask,id))

def c12118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12118 : Upper (D 8) (R 8) [66,260,160,48,192] 13 := by
  apply FastRouting.sound _ _ [66,260,160,48,192] 13 (by decide) (choices 1) [1,8] r12118 c12118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3905
  · exact u3906

def b12119 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 73 152 49 113 177 305), lower := (rows 67 262 164 73 152 32 64 128 256), losses := [] }

theorem u12119 : Upper (D 8) (R 8) [66,260,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12119
end Delivery.IrregularNine14.P08
