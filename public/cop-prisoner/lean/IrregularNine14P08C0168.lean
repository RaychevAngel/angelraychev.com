import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0046

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10080 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 7 292 25 88 160 224 160 416), lower := (rows 67 7 292 25 88 32 64 128 256), losses := [] }

theorem u10080 : Upper (D 8) (R 8) [66,5,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10081 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 112 168 232 168 424), lower := (rows 67 7 292 25 112 32 64 128 256), losses := [] }

theorem u10081 : Upper (D 8) (R 8) [66,5,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10082 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 152 224 224 224 480), lower := (rows 67 7 292 25 152 32 64 128 256), losses := [] }

theorem u10082 : Upper (D 8) (R 8) [66,5,288,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10083 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 176 232 232 232 488), lower := (rows 67 7 292 25 176 32 64 128 256), losses := [] }

theorem u10083 : Upper (D 8) (R 8) [66,5,288,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10084 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 208 168 232 168 424), lower := (rows 67 7 292 25 208 32 64 128 256), losses := [] }

theorem u10084 : Upper (D 8) (R 8) [66,5,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10085 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 56 240 208 208 464), lower := (rows 67 7 292 41 56 32 64 128 256), losses := [] }

theorem u10085 : Upper (D 8) (R 8) [66,5,288,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10086 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 88 176 240 176 432), lower := (rows 67 7 292 41 88 32 64 128 256), losses := [] }

theorem u10086 : Upper (D 8) (R 8) [66,5,288,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10087 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 112 184 216 152 408), lower := (rows 67 7 292 41 112 32 64 128 256), losses := [] }

theorem u10087 : Upper (D 8) (R 8) [66,5,288,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10088 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 152 240 240 240 496), lower := (rows 67 7 292 41 152 32 64 128 256), losses := [] }

theorem u10088 : Upper (D 8) (R 8) [66,5,288,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10089 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 176 248 216 216 472), lower := (rows 67 7 292 41 176 32 64 128 256), losses := [] }

theorem u10089 : Upper (D 8) (R 8) [66,5,288,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10090 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 208 184 248 184 440), lower := (rows 67 7 292 41 208 32 64 128 256), losses := [] }

theorem u10090 : Upper (D 8) (R 8) [66,5,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10091 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 292 56 56 225 193 193 449), lower := (rows 67 7 292 56 56 32 64 128 256), losses := [] }

theorem u10091 : Upper (D 8) (R 8) [66,5,288,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10092 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 56 81 168 232 168 424), lower := (rows 67 7 292 56 81 32 64 128 256), losses := [] }

theorem u10092 : Upper (D 8) (R 8) [66,5,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10093 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 56 88 161 225 161 417), lower := (rows 67 7 292 56 88 32 64 128 256), losses := [] }

theorem u10093 : Upper (D 8) (R 8) [66,5,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10094 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 292 56 112 169 201 137 393), lower := (rows 67 7 292 56 112 32 64 128 256), losses := [] }

theorem u10094 : Upper (D 8) (R 8) [66,5,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10095 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 56 145 232 232 232 488), lower := (rows 67 7 292 56 145 32 64 128 256), losses := [] }

theorem u10095 : Upper (D 8) (R 8) [66,5,288,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10096 : Route 9 := (fun mask => (mask,id))

def c10096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10096 : Upper (D 8) (R 8) [66,5,288,48,136] 13 := by
  apply FastRouting.sound _ _ [66,5,288,48,136] 13 (by decide) (choices 1) [1,64,128] r10096 c10096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2770
  · exact u2771
  · exact u2772

def b10097 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 292 56 176 233 201 201 457), lower := (rows 67 7 292 56 176 32 64 128 256), losses := [] }

theorem u10097 : Upper (D 8) (R 8) [66,5,288,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10098 : Route 9 := (fun mask => (mask,id))

def c10098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10098 : Upper (D 8) (R 8) [66,5,288,48,192] 13 := by
  apply FastRouting.sound _ _ [66,5,288,48,192] 13 (by decide) (choices 1) [1,8,128] r10098 c10098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2773
  · exact u2774
  · exact u2775

def b10099 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 73 152 176 240 176 432), lower := (rows 67 7 292 73 152 32 64 128 256), losses := [] }

theorem u10099 : Upper (D 8) (R 8) [66,5,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10100 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 73 176 184 248 184 440), lower := (rows 67 7 292 73 176 32 64 128 256), losses := [] }

theorem u10100 : Upper (D 8) (R 8) [66,5,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10101 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 88 145 168 232 168 424), lower := (rows 67 7 292 88 145 32 64 128 256), losses := [] }

theorem u10101 : Upper (D 8) (R 8) [66,5,288,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10102 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 88 152 161 225 161 417), lower := (rows 67 7 292 88 152 32 64 128 256), losses := [] }

theorem u10102 : Upper (D 8) (R 8) [66,5,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10103 : Route 9 := (fun mask => (mask,id))

def c10103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10103 : Upper (D 8) (R 8) [66,5,288,80,160] 13 := by
  apply FastRouting.sound _ _ [66,5,288,80,160] 13 (by decide) (choices 1) [1,8,128] r10103 c10103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2776
  · exact u2777
  · exact u2778

def b10104 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 104 145 184 248 184 440), lower := (rows 67 7 292 104 145 32 64 128 256), losses := [] }

theorem u10104 : Upper (D 8) (R 8) [66,5,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10105 : Route 9 := (fun mask => (mask,id))

def c10105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10105 : Upper (D 8) (R 8) [66,5,288,96,136] 13 := by
  apply FastRouting.sound _ _ [66,5,288,96,136] 13 (by decide) (choices 1) [1,16,128] r10105 c10105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2779
  · exact u2780
  · exact u2781

def r10106 : Route 9 := (fun mask => (mask,id))

def c10106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10106 : Upper (D 8) (R 8) [66,5,288,96,160] 13 := by
  apply FastRouting.sound _ _ [66,5,288,96,160] 13 (by decide) (choices 1) [1,8,16,128] r10106 c10106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2782
  · exact u2783
  · exact u2784
  · exact u2785

def b10107 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 137 152 112 112 240 368), lower := (rows 67 7 292 137 152 32 64 128 256), losses := [] }

theorem u10107 : Upper (D 8) (R 8) [66,5,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10108 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 137 176 120 120 248 376), lower := (rows 67 7 292 137 176 32 64 128 256), losses := [] }

theorem u10108 : Upper (D 8) (R 8) [66,5,288,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10109 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 137 208 56 120 184 312), lower := (rows 67 7 292 137 208 32 64 128 256), losses := [] }

theorem u10109 : Upper (D 8) (R 8) [66,5,288,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10110 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 292 152 152 97 97 225 353), lower := (rows 67 7 292 152 152 32 64 128 256), losses := [] }

theorem u10110 : Upper (D 8) (R 8) [66,5,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10111 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 152 176 105 105 233 361), lower := (rows 67 7 292 152 176 32 64 128 256), losses := [] }

theorem u10111 : Upper (D 8) (R 8) [66,5,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10112 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 152 208 41 105 169 297), lower := (rows 67 7 292 152 208 32 64 128 256), losses := [] }

theorem u10112 : Upper (D 8) (R 8) [66,5,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10113 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 292 168 176 121 89 217 345), lower := (rows 67 7 292 168 176 32 64 128 256), losses := [] }

theorem u10113 : Upper (D 8) (R 8) [66,5,288,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10114 : Route 9 := (fun mask => (mask,id))

def c10114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10114 : Upper (D 8) (R 8) [66,5,288,160,192] 13 := by
  apply FastRouting.sound _ _ [66,5,288,160,192] 13 (by decide) (choices 1) [1,8,16] r10114 c10114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2786
  · exact u2787
  · exact u2788

def b10115 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 25 56 224 224 224 480), lower := (rows 67 7 388 25 56 32 64 128 256), losses := [] }

theorem u10115 : Upper (D 8) (R 8) [66,5,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10116 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 7 388 25 88 160 224 160 416), lower := (rows 67 7 388 25 88 32 64 128 256), losses := [] }

theorem u10116 : Upper (D 8) (R 8) [66,5,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10117 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 25 112 168 232 168 424), lower := (rows 67 7 388 25 112 32 64 128 256), losses := [] }

theorem u10117 : Upper (D 8) (R 8) [66,5,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10118 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 388 25 152 96 96 224 352), lower := (rows 67 7 388 25 152 32 64 128 256), losses := [] }

theorem u10118 : Upper (D 8) (R 8) [66,5,384,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10119 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 25 176 104 104 232 360), lower := (rows 67 7 388 25 176 32 64 128 256), losses := [] }

theorem u10119 : Upper (D 8) (R 8) [66,5,384,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10120 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 25 208 40 104 168 296), lower := (rows 67 7 388 25 208 32 64 128 256), losses := [] }

theorem u10120 : Upper (D 8) (R 8) [66,5,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10121 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 56 240 240 240 496), lower := (rows 67 7 388 41 56 32 64 128 256), losses := [] }

theorem u10121 : Upper (D 8) (R 8) [66,5,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10122 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 88 176 240 176 432), lower := (rows 67 7 388 41 88 32 64 128 256), losses := [] }

theorem u10122 : Upper (D 8) (R 8) [66,5,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10123 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 112 184 248 184 440), lower := (rows 67 7 388 41 112 32 64 128 256), losses := [] }

theorem u10123 : Upper (D 8) (R 8) [66,5,384,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10124 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 152 112 112 240 368), lower := (rows 67 7 388 41 152 32 64 128 256), losses := [] }

theorem u10124 : Upper (D 8) (R 8) [66,5,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10125 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 176 120 120 248 376), lower := (rows 67 7 388 41 176 32 64 128 256), losses := [] }

theorem u10125 : Upper (D 8) (R 8) [66,5,384,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10126 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 208 56 120 184 312), lower := (rows 67 7 388 41 208 32 64 128 256), losses := [] }

theorem u10126 : Upper (D 8) (R 8) [66,5,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10127 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 388 56 56 225 225 225 481), lower := (rows 67 7 388 56 56 32 64 128 256), losses := [] }

theorem u10127 : Upper (D 8) (R 8) [66,5,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10128 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 56 81 168 232 168 424), lower := (rows 67 7 388 56 81 32 64 128 256), losses := [] }

theorem u10128 : Upper (D 8) (R 8) [66,5,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10129 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 56 88 161 225 161 417), lower := (rows 67 7 388 56 88 32 64 128 256), losses := [] }

theorem u10129 : Upper (D 8) (R 8) [66,5,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10130 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 388 56 112 169 233 169 425), lower := (rows 67 7 388 56 112 32 64 128 256), losses := [] }

theorem u10130 : Upper (D 8) (R 8) [66,5,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10131 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 56 145 104 104 232 360), lower := (rows 67 7 388 56 145 32 64 128 256), losses := [] }

theorem u10131 : Upper (D 8) (R 8) [66,5,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10132 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 388 56 152 97 97 225 353), lower := (rows 67 7 388 56 152 32 64 128 256), losses := [] }

theorem u10132 : Upper (D 8) (R 8) [66,5,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10133 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 388 56 176 105 105 233 361), lower := (rows 67 7 388 56 176 32 64 128 256), losses := [] }

theorem u10133 : Upper (D 8) (R 8) [66,5,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10134 : Route 9 := (fun mask => (mask,id))

def c10134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10134 : Upper (D 8) (R 8) [66,5,384,48,192] 13 := by
  apply FastRouting.sound _ _ [66,5,384,48,192] 13 (by decide) (choices 1) [1,8] r10134 c10134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2789
  · exact u2790

def b10135 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 73 152 48 112 176 304), lower := (rows 67 7 388 73 152 32 64 128 256), losses := [] }

theorem u10135 : Upper (D 8) (R 8) [66,5,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10136 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 73 176 56 120 184 312), lower := (rows 67 7 388 73 176 32 64 128 256), losses := [] }

theorem u10136 : Upper (D 8) (R 8) [66,5,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10137 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 88 145 40 104 168 296), lower := (rows 67 7 388 88 145 32 64 128 256), losses := [] }

theorem u10137 : Upper (D 8) (R 8) [66,5,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10138 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 88 152 33 97 161 289), lower := (rows 67 7 388 88 152 32 64 128 256), losses := [] }

theorem u10138 : Upper (D 8) (R 8) [66,5,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10139 : Route 9 := (fun mask => (mask,id))

def c10139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10139 : Upper (D 8) (R 8) [66,5,384,80,160] 13 := by
  apply FastRouting.sound _ _ [66,5,384,80,160] 13 (by decide) (choices 1) [1,8] r10139 c10139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2791
  · exact u2792

#print axioms u10139
end Delivery.IrregularNine14.P08
