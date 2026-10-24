import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0063
import IrregularNine14P08C0064

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12000 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 112 184 216 152 408), lower := (rows 67 262 37 41 112 32 64 128 256), losses := [] }

theorem u12000 : Upper (D 8) (R 8) [66,260,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12001 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 152 240 240 240 496), lower := (rows 67 262 37 41 152 32 64 128 256), losses := [] }

theorem u12001 : Upper (D 8) (R 8) [66,260,33,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12002 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 176 248 216 216 472), lower := (rows 67 262 37 41 176 32 64 128 256), losses := [] }

theorem u12002 : Upper (D 8) (R 8) [66,260,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12003 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 262 37 41 208 184 248 184 440), lower := (rows 67 262 37 41 208 32 64 128 256), losses := [] }

theorem u12003 : Upper (D 8) (R 8) [66,260,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12004 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 56 56 225 193 193 449), lower := (rows 67 262 37 56 56 32 64 128 256), losses := [] }

theorem u12004 : Upper (D 8) (R 8) [66,260,33,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12005 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 56 81 168 232 168 424), lower := (rows 67 262 37 56 81 32 64 128 256), losses := [] }

theorem u12005 : Upper (D 8) (R 8) [66,260,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12006 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 56 88 161 225 161 417), lower := (rows 67 262 37 56 88 32 64 128 256), losses := [] }

theorem u12006 : Upper (D 8) (R 8) [66,260,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12007 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 56 112 169 201 137 393), lower := (rows 67 262 37 56 112 32 64 128 256), losses := [] }

theorem u12007 : Upper (D 8) (R 8) [66,260,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12008 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 56 145 232 232 232 488), lower := (rows 67 262 37 56 145 32 64 128 256), losses := [] }

theorem u12008 : Upper (D 8) (R 8) [66,260,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12009 : Route 9 := (fun mask => (mask,id))

def c12009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12009 : Upper (D 8) (R 8) [66,260,33,48,136] 13 := by
  apply FastRouting.sound _ _ [66,260,33,48,136] 13 (by decide) (choices 1) [1,64,128] r12009 c12009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3834
  · exact u3835
  · exact u3836

def b12010 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 56 176 233 201 201 457), lower := (rows 67 262 37 56 176 32 64 128 256), losses := [] }

theorem u12010 : Upper (D 8) (R 8) [66,260,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12011 : Route 9 := (fun mask => (mask,id))

def c12011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12011 : Upper (D 8) (R 8) [66,260,33,48,192] 13 := by
  apply FastRouting.sound _ _ [66,260,33,48,192] 13 (by decide) (choices 1) [1,8,128] r12011 c12011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3837
  · exact u3838
  · exact u3839

def b12012 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 73 152 176 240 176 432), lower := (rows 67 262 37 73 152 32 64 128 256), losses := [] }

theorem u12012 : Upper (D 8) (R 8) [66,260,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12013 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 73 176 184 248 184 440), lower := (rows 67 262 37 73 176 32 64 128 256), losses := [] }

theorem u12013 : Upper (D 8) (R 8) [66,260,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12014 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 88 145 168 232 168 424), lower := (rows 67 262 37 88 145 32 64 128 256), losses := [] }

theorem u12014 : Upper (D 8) (R 8) [66,260,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12015 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 88 152 161 225 161 417), lower := (rows 67 262 37 88 152 32 64 128 256), losses := [] }

theorem u12015 : Upper (D 8) (R 8) [66,260,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12016 : Route 9 := (fun mask => (mask,id))

def c12016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12016 : Upper (D 8) (R 8) [66,260,33,80,160] 13 := by
  apply FastRouting.sound _ _ [66,260,33,80,160] 13 (by decide) (choices 1) [1,8,128] r12016 c12016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3840
  · exact u3841
  · exact u3842

def b12017 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 104 145 184 248 184 440), lower := (rows 67 262 37 104 145 32 64 128 256), losses := [] }

theorem u12017 : Upper (D 8) (R 8) [66,260,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12018 : Route 9 := (fun mask => (mask,id))

def c12018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12018 : Upper (D 8) (R 8) [66,260,33,96,136] 13 := by
  apply FastRouting.sound _ _ [66,260,33,96,136] 13 (by decide) (choices 1) [1,16,128] r12018 c12018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3843
  · exact u3844
  · exact u3845

def r12019 : Route 9 := (fun mask => (mask,id))

def c12019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12019 : Upper (D 8) (R 8) [66,260,33,96,160] 13 := by
  apply FastRouting.sound _ _ [66,260,33,96,160] 13 (by decide) (choices 1) [1,8,16,128] r12019 c12019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3846
  · exact u3847
  · exact u3848
  · exact u3849

def b12020 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 137 152 112 112 240 368), lower := (rows 67 262 37 137 152 32 64 128 256), losses := [] }

theorem u12020 : Upper (D 8) (R 8) [66,260,33,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12021 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 137 176 120 120 248 376), lower := (rows 67 262 37 137 176 32 64 128 256), losses := [] }

theorem u12021 : Upper (D 8) (R 8) [66,260,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12022 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 137 208 56 120 184 312), lower := (rows 67 262 37 137 208 32 64 128 256), losses := [] }

theorem u12022 : Upper (D 8) (R 8) [66,260,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12023 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 152 152 97 97 225 353), lower := (rows 67 262 37 152 152 32 64 128 256), losses := [] }

theorem u12023 : Upper (D 8) (R 8) [66,260,33,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12024 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 152 176 105 105 233 361), lower := (rows 67 262 37 152 176 32 64 128 256), losses := [] }

theorem u12024 : Upper (D 8) (R 8) [66,260,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12025 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 152 208 41 105 169 297), lower := (rows 67 262 37 152 208 32 64 128 256), losses := [] }

theorem u12025 : Upper (D 8) (R 8) [66,260,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12026 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 37 168 176 121 89 217 345), lower := (rows 67 262 37 168 176 32 64 128 256), losses := [] }

theorem u12026 : Upper (D 8) (R 8) [66,260,33,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12027 : Route 9 := (fun mask => (mask,id))

def c12027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12027 : Upper (D 8) (R 8) [66,260,33,160,192] 13 := by
  apply FastRouting.sound _ _ [66,260,33,160,192] 13 (by decide) (choices 1) [1,8,16] r12027 c12027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3850
  · exact u3851
  · exact u3852

def b12028 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 262 44 25 49 224 224 224 480), lower := (rows 67 262 44 25 49 32 64 128 256), losses := [] }

theorem u12028 : Upper (D 8) (R 8) [66,260,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12029 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 44 25 81 160 224 160 416), lower := (rows 67 262 44 25 81 32 64 128 256), losses := [] }

theorem u12029 : Upper (D 8) (R 8) [66,260,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12030 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 25 112 161 225 161 417), lower := (rows 67 262 44 25 112 32 64 128 256), losses := [] }

theorem u12030 : Upper (D 8) (R 8) [66,260,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12031 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 44 25 145 224 224 224 480), lower := (rows 67 262 44 25 145 32 64 128 256), losses := [] }

theorem u12031 : Upper (D 8) (R 8) [66,260,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12032 : Route 9 := (fun mask => (mask,id))

def c12032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12032 : Upper (D 8) (R 8) [66,260,40,17,160] 13 := by
  apply FastRouting.sound _ _ [66,260,40,17,160] 13 (by decide) (choices 1) [1,64,128] r12032 c12032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3853
  · exact u3854
  · exact u3855

def b12033 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 25 208 161 225 161 417), lower := (rows 67 262 44 25 208 32 64 128 256), losses := [] }

theorem u12033 : Upper (D 8) (R 8) [66,260,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12034 : Route 9 := (fun mask => (mask,id))

def c12034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12034 : Upper (D 8) (R 8) [66,260,40,129,33] 13 := by
  apply FastRouting.sound _ _ [66,260,40,129,33] 13 (by decide) (choices 1) [16,64,128] r12034 c12034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3856
  · exact u3857
  · exact u3858

def b12035 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 137 81 176 240 176 432), lower := (rows 67 262 44 137 81 32 64 128 256), losses := [] }

theorem u12035 : Upper (D 8) (R 8) [66,260,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12036 : Route 9 := (fun mask => (mask,id))

def c12036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12036 : Upper (D 8) (R 8) [66,260,40,129,96] 13 := by
  apply FastRouting.sound _ _ [66,260,40,129,96] 13 (by decide) (choices 1) [1,16,128] r12036 c12036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3859
  · exact u3860
  · exact u3861

def b12037 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 262 44 137 145 112 112 240 368), lower := (rows 67 262 44 137 145 32 64 128 256), losses := [] }

theorem u12037 : Upper (D 8) (R 8) [66,260,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12038 : Route 9 := (fun mask => (mask,id))

def c12038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12038 : Upper (D 8) (R 8) [66,260,40,129,160] 13 := by
  apply FastRouting.sound _ _ [66,260,40,129,160] 13 (by decide) (choices 1) [1,16,64] r12038 c12038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3862
  · exact u3863
  · exact u3864

def r12039 : Route 9 := (fun mask => (mask,id))

def c12039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12039 : Upper (D 8) (R 8) [66,260,40,129,192] 13 := by
  apply FastRouting.sound _ _ [66,260,40,129,192] 13 (by decide) (choices 1) [1,16] r12039 c12039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3865
  · exact u3866

def r12040 : Route 9 := (fun mask => (mask,id))

def c12040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12040 : Upper (D 8) (R 8) [66,260,40,144,33] 13 := by
  apply FastRouting.sound _ _ [66,260,40,144,33] 13 (by decide) (choices 1) [1,64,128] r12040 c12040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3867
  · exact u3868
  · exact u3869

def b12041 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 44 152 81 161 225 161 417), lower := (rows 67 262 44 152 81 32 64 128 256), losses := [] }

theorem u12041 : Upper (D 8) (R 8) [66,260,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12042 : Route 9 := (fun mask => (mask,id))

def c12042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12042 : Upper (D 8) (R 8) [66,260,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,260,40,144,96] 13 (by decide) (choices 1) [1,128] r12042 c12042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3870
  · exact u3871

def b12043 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 152 145 97 97 225 353), lower := (rows 67 262 44 152 145 32 64 128 256), losses := [] }

theorem u12043 : Upper (D 8) (R 8) [66,260,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12044 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 262 44 152 176 97 97 225 353), lower := (rows 67 262 44 152 176 32 64 128 256), losses := [] }

theorem u12044 : Upper (D 8) (R 8) [66,260,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12045 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 44 152 208 33 97 161 289), lower := (rows 67 262 44 152 208 32 64 128 256), losses := [] }

theorem u12045 : Upper (D 8) (R 8) [66,260,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12046 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 133 25 56 224 224 224 480), lower := (rows 67 262 133 25 56 32 64 128 256), losses := [] }

theorem u12046 : Upper (D 8) (R 8) [66,260,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12047 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 133 25 88 160 224 160 416), lower := (rows 67 262 133 25 88 32 64 128 256), losses := [] }

theorem u12047 : Upper (D 8) (R 8) [66,260,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12048 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 25 112 168 232 168 424), lower := (rows 67 262 133 25 112 32 64 128 256), losses := [] }

theorem u12048 : Upper (D 8) (R 8) [66,260,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12049 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 262 133 25 152 96 96 224 352), lower := (rows 67 262 133 25 152 32 64 128 256), losses := [] }

theorem u12049 : Upper (D 8) (R 8) [66,260,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12050 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 25 176 104 104 232 360), lower := (rows 67 262 133 25 176 32 64 128 256), losses := [] }

theorem u12050 : Upper (D 8) (R 8) [66,260,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12051 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 25 208 40 104 168 296), lower := (rows 67 262 133 25 208 32 64 128 256), losses := [] }

theorem u12051 : Upper (D 8) (R 8) [66,260,129,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12052 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 262 133 41 56 240 240 240 496), lower := (rows 67 262 133 41 56 32 64 128 256), losses := [] }

theorem u12052 : Upper (D 8) (R 8) [66,260,129,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12053 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 88 176 240 176 432), lower := (rows 67 262 133 41 88 32 64 128 256), losses := [] }

theorem u12053 : Upper (D 8) (R 8) [66,260,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12054 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 112 184 248 184 440), lower := (rows 67 262 133 41 112 32 64 128 256), losses := [] }

theorem u12054 : Upper (D 8) (R 8) [66,260,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12055 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 152 112 112 240 368), lower := (rows 67 262 133 41 152 32 64 128 256), losses := [] }

theorem u12055 : Upper (D 8) (R 8) [66,260,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12056 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 176 120 120 248 376), lower := (rows 67 262 133 41 176 32 64 128 256), losses := [] }

theorem u12056 : Upper (D 8) (R 8) [66,260,129,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12057 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 133 41 208 56 120 184 312), lower := (rows 67 262 133 41 208 32 64 128 256), losses := [] }

theorem u12057 : Upper (D 8) (R 8) [66,260,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12058 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 133 56 56 225 225 225 481), lower := (rows 67 262 133 56 56 32 64 128 256), losses := [] }

theorem u12058 : Upper (D 8) (R 8) [66,260,129,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12059 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 133 56 81 168 232 168 424), lower := (rows 67 262 133 56 81 32 64 128 256), losses := [] }

theorem u12059 : Upper (D 8) (R 8) [66,260,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12059
end Delivery.IrregularNine14.P08
