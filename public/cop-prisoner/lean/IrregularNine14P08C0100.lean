import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0012

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6000 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 56 208 33 232 168 424), lower := (rows 259 70 37 56 208 33 64 128 256), losses := [] }

theorem u6000 : Upper (D 8) (R 8) [258,68,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6001 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 37 56 208 40 225 161 417), lower := (rows 259 70 37 56 208 40 64 128 256), losses := [] }

theorem u6001 : Upper (D 8) (R 8) [258,68,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6001 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6002 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 56 208 160 105 169 297), lower := (rows 259 70 37 56 208 160 64 128 256), losses := [] }

theorem u6002 : Upper (D 8) (R 8) [258,68,33,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6003 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 88 176 33 232 168 424), lower := (rows 259 70 37 88 176 33 64 128 256), losses := [] }

theorem u6003 : Upper (D 8) (R 8) [258,68,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 37 88 176 40 225 161 417), lower := (rows 259 70 37 88 176 40 64 128 256), losses := [] }

theorem u6004 : Upper (D 8) (R 8) [258,68,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6004 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6005 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 88 176 160 105 169 297), lower := (rows 259 70 37 88 176 160 64 128 256), losses := [] }

theorem u6005 : Upper (D 8) (R 8) [258,68,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 104 152 33 240 176 432), lower := (rows 259 70 37 104 152 33 64 128 256), losses := [] }

theorem u6006 : Upper (D 8) (R 8) [258,68,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 37 104 152 48 225 161 417), lower := (rows 259 70 37 104 152 48 64 128 256), losses := [] }

theorem u6007 : Upper (D 8) (R 8) [258,68,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6007 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6008 : Route 9 := (fun mask => (mask,id))

def c6008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6008 : Upper (D 8) (R 8) [258,68,33,96,136,128] 13 := by
  apply FastRouting.sound _ _ [258,68,33,96,136,128] 13 (by decide) (choices 1) [1,16,32] r6008 c6008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u742
  · exact u743
  · exact u744

def b6009 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 104 176 33 216 152 408), lower := (rows 259 70 37 104 176 33 64 128 256), losses := [] }

theorem u6009 : Upper (D 8) (R 8) [258,68,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6010 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 70 37 104 176 40 209 145 401), lower := (rows 259 70 37 104 176 40 64 128 256), losses := [] }

theorem u6010 : Upper (D 8) (R 8) [258,68,33,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6010 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6011 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 70 37 104 176 48 201 137 393), lower := (rows 259 70 37 104 176 48 64 128 256), losses := [] }

theorem u6011 : Upper (D 8) (R 8) [258,68,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6011 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6012 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 104 176 160 89 153 281), lower := (rows 259 70 37 104 176 160 64 128 256), losses := [] }

theorem u6012 : Upper (D 8) (R 8) [258,68,33,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 168 208 33 120 184 312), lower := (rows 259 70 37 168 208 33 64 128 256), losses := [] }

theorem u6013 : Upper (D 8) (R 8) [258,68,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6014 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 70 37 168 208 40 113 177 305), lower := (rows 259 70 37 168 208 40 64 128 256), losses := [] }

theorem u6014 : Upper (D 8) (R 8) [258,68,33,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6014 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6015 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 70 37 168 208 48 105 169 297), lower := (rows 259 70 37 168 208 48 64 128 256), losses := [] }

theorem u6015 : Upper (D 8) (R 8) [258,68,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6015 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6016 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 25 176 33 224 224 480), lower := (rows 259 70 44 25 176 33 64 128 256), losses := [] }

theorem u6016 : Upper (D 8) (R 8) [258,68,40,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6017 : Route 9 := (fun mask => (mask,id))

def c6017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6017 : Upper (D 8) (R 8) [258,68,40,17,160,64] 13 := by
  apply FastRouting.sound _ _ [258,68,40,17,160,64] 13 (by decide) (choices 1) [1,32,128] r6017 c6017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u745
  · exact u746
  · exact u747

def b6018 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 25 176 160 97 225 353), lower := (rows 259 70 44 25 176 160 64 128 256), losses := [] }

theorem u6018 : Upper (D 8) (R 8) [258,68,40,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6019 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 70 44 137 49 48 224 224 480), lower := (rows 259 70 44 137 49 48 64 128 256), losses := [] }

theorem u6019 : Upper (D 8) (R 8) [258,68,40,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6019 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6020 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 44 137 49 96 240 176 432), lower := (rows 259 70 44 137 49 96 64 128 256), losses := [] }

theorem u6020 : Upper (D 8) (R 8) [258,68,40,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 137 49 160 112 240 368), lower := (rows 259 70 44 137 49 160 64 128 256), losses := [] }

theorem u6021 : Upper (D 8) (R 8) [258,68,40,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6022 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 137 112 33 240 176 432), lower := (rows 259 70 44 137 112 33 64 128 256), losses := [] }

theorem u6022 : Upper (D 8) (R 8) [258,68,40,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6023 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 44 137 112 48 225 161 417), lower := (rows 259 70 44 137 112 48 64 128 256), losses := [] }

theorem u6023 : Upper (D 8) (R 8) [258,68,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6023 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6024 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 137 112 160 113 177 305), lower := (rows 259 70 44 137 112 160 64 128 256), losses := [] }

theorem u6024 : Upper (D 8) (R 8) [258,68,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6025 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 137 176 33 112 240 368), lower := (rows 259 70 44 137 176 33 64 128 256), losses := [] }

theorem u6025 : Upper (D 8) (R 8) [258,68,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6026 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 259 70 44 137 176 48 97 225 353), lower := (rows 259 70 44 137 176 48 64 128 256), losses := [] }

theorem u6026 : Upper (D 8) (R 8) [258,68,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6026 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6027 : Route 9 := (fun mask => (mask,id))

def c6027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6027 : Upper (D 8) (R 8) [258,68,40,129,160,64] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129,160,64] 13 (by decide) (choices 1) [1,16,32] r6027 c6027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u748
  · exact u749
  · exact u750

def b6028 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 137 208 33 112 176 304), lower := (rows 259 70 44 137 208 33 64 128 256), losses := [] }

theorem u6028 : Upper (D 8) (R 8) [258,68,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 44 137 208 48 97 161 289), lower := (rows 259 70 44 137 208 48 64 128 256), losses := [] }

theorem u6029 : Upper (D 8) (R 8) [258,68,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6029 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6030 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 152 49 33 224 224 480), lower := (rows 259 70 44 152 49 33 64 128 256), losses := [] }

theorem u6030 : Upper (D 8) (R 8) [258,68,40,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6031 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 44 152 49 96 225 161 417), lower := (rows 259 70 44 152 49 96 64 128 256), losses := [] }

theorem u6031 : Upper (D 8) (R 8) [258,68,40,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 152 49 160 97 225 353), lower := (rows 259 70 44 152 49 160 64 128 256), losses := [] }

theorem u6032 : Upper (D 8) (R 8) [258,68,40,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6033 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 56 208 33 104 168 296), lower := (rows 259 70 133 56 208 33 64 128 256), losses := [] }

theorem u6033 : Upper (D 8) (R 8) [258,68,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 133 56 208 40 97 161 289), lower := (rows 259 70 133 56 208 40 64 128 256), losses := [] }

theorem u6034 : Upper (D 8) (R 8) [258,68,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6034 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 88 176 33 104 168 296), lower := (rows 259 70 133 88 176 33 64 128 256), losses := [] }

theorem u6035 : Upper (D 8) (R 8) [258,68,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 133 88 176 40 97 161 289), lower := (rows 259 70 133 88 176 40 64 128 256), losses := [] }

theorem u6036 : Upper (D 8) (R 8) [258,68,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6036 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6037 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 104 152 33 112 176 304), lower := (rows 259 70 133 104 152 33 64 128 256), losses := [] }

theorem u6037 : Upper (D 8) (R 8) [258,68,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6038 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 133 104 152 48 97 161 289), lower := (rows 259 70 133 104 152 48 64 128 256), losses := [] }

theorem u6038 : Upper (D 8) (R 8) [258,68,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6038 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6039 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 104 176 33 120 184 312), lower := (rows 259 70 133 104 176 33 64 128 256), losses := [] }

theorem u6039 : Upper (D 8) (R 8) [258,68,129,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6040 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 70 133 104 176 40 113 177 305), lower := (rows 259 70 133 104 176 40 64 128 256), losses := [] }

theorem u6040 : Upper (D 8) (R 8) [258,68,129,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6040 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6041 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 70 133 104 176 48 105 169 297), lower := (rows 259 70 133 104 176 48 64 128 256), losses := [] }

theorem u6041 : Upper (D 8) (R 8) [258,68,129,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6041 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6042 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 140 41 112 33 240 176 432), lower := (rows 259 70 140 41 112 33 64 128 256), losses := [] }

theorem u6042 : Upper (D 8) (R 8) [258,68,136,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6043 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 140 41 112 48 225 161 417), lower := (rows 259 70 140 41 112 48 64 128 256), losses := [] }

theorem u6043 : Upper (D 8) (R 8) [258,68,136,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6043 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6044 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 259 70 140 41 112 160 113 177 305), lower := (rows 259 70 140 41 112 160 64 128 256), losses := [] }

theorem u6044 : Upper (D 8) (R 8) [258,68,136,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6045 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 140 41 176 33 112 240 368), lower := (rows 259 70 140 41 176 33 64 128 256), losses := [] }

theorem u6045 : Upper (D 8) (R 8) [258,68,136,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 259 70 140 41 176 48 97 225 353), lower := (rows 259 70 140 41 176 48 64 128 256), losses := [] }

theorem u6046 : Upper (D 8) (R 8) [258,68,136,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6046 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6047 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 148, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 140 41 176 96 113 177 305), lower := (rows 259 70 140 41 176 96 64 128 256), losses := [] }

theorem u6047 : Upper (D 8) (R 8) [258,68,136,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6048 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 140 41 208 33 112 176 304), lower := (rows 259 70 140 41 208 33 64 128 256), losses := [] }

theorem u6048 : Upper (D 8) (R 8) [258,68,136,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6049 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 140 41 208 48 97 161 289), lower := (rows 259 70 140 41 208 48 64 128 256), losses := [] }

theorem u6049 : Upper (D 8) (R 8) [258,68,136,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6049 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6050 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 164 25 56 33 224 224 480), lower := (rows 259 70 164 25 56 33 64 128 256), losses := [] }

theorem u6050 : Upper (D 8) (R 8) [258,68,160,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6051 : PairBound 9 := { available := 161, camps := [], pairs := [(3,7)], upper := (rows 259 70 164 25 56 96 225 161 417), lower := (rows 259 70 164 25 56 96 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 17 98 64 0 256), good := (rows 315 102 36 25 56 96 96 0 256) }] }

theorem u6051 : Upper (D 8) (R 8) [258,68,160,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6052 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 164 25 56 160 97 225 353), lower := (rows 259 70 164 25 56 160 64 128 256), losses := [] }

theorem u6052 : Upper (D 8) (R 8) [258,68,160,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 41 88 33 240 176 432), lower := (rows 259 70 164 41 88 33 64 128 256), losses := [] }

theorem u6053 : Upper (D 8) (R 8) [258,68,160,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6054 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 70 164 41 88 48 225 161 417), lower := (rows 259 70 164 41 88 48 64 128 256), losses := [] }

theorem u6054 : Upper (D 8) (R 8) [258,68,160,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6054 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6055 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 164 41 88 160 113 177 305), lower := (rows 259 70 164 41 88 160 64 128 256), losses := [] }

theorem u6055 : Upper (D 8) (R 8) [258,68,160,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 41 112 33 216 152 408), lower := (rows 259 70 164 41 112 33 64 128 256), losses := [] }

theorem u6056 : Upper (D 8) (R 8) [258,68,160,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6057 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 70 164 41 112 40 209 145 401), lower := (rows 259 70 164 41 112 40 64 128 256), losses := [] }

theorem u6057 : Upper (D 8) (R 8) [258,68,160,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6057 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 70 164 41 112 48 201 137 393), lower := (rows 259 70 164 41 112 48 64 128 256), losses := [] }

theorem u6058 : Upper (D 8) (R 8) [258,68,160,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6058 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 164 41 112 160 89 153 281), lower := (rows 259 70 164 41 112 160 64 128 256), losses := [] }

theorem u6059 : Upper (D 8) (R 8) [258,68,160,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P08
