import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 69 265 50 160 66 144 400), lower := (rows 37 74 69 265 50 160 66 128 256), losses := [] }

theorem u7140 : Upper (D 7) (R 7) [36,72,65,257,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7141 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 265 50 160 80 130 386), lower := (rows 37 74 69 265 50 160 80 128 256), losses := [] }

theorem u7141 : Upper (D 7) (R 7) [36,72,65,257,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7141 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7142 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 74 69 265 50 160 192 146 274), lower := (rows 37 74 69 265 50 160 192 128 256), losses := [] }

theorem u7142 : Upper (D 7) (R 7) [36,72,65,257,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7143 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 69 265 146 160 66 176 304), lower := (rows 37 74 69 265 146 160 66 128 256), losses := [] }

theorem u7143 : Upper (D 7) (R 7) [36,72,65,257,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7144 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 74 69 265 146 160 80 162 290), lower := (rows 37 74 69 265 146 160 80 128 256), losses := [] }

theorem u7144 : Upper (D 7) (R 7) [36,72,65,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7144 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7145 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 265 146 160 96 146 274), lower := (rows 37 74 69 265 146 160 96 128 256), losses := [] }

theorem u7145 : Upper (D 7) (R 7) [36,72,65,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7146 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 266 50 160 65 144 400), lower := (rows 37 74 69 266 50 160 65 128 256), losses := [] }

theorem u7146 : Upper (D 7) (R 7) [36,72,65,258,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 2, region := 394, targets := 32 }], pairs := [(0,1),(1,5),(2,1)], upper := (rows 37 74 69 266 50 160 80 129 385), lower := (rows 37 74 69 266 50 160 80 128 256), losses := [] }

theorem u7147 : Upper (D 7) (R 7) [36,72,65,258,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7147 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7148 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(2,5),(4,0)], upper := (rows 37 74 69 266 50 160 192 145 273), lower := (rows 37 74 69 266 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 122 100 282 114 224 224 224 256) },{ target := 5, region := (rows 1 2 5 8 16 0 224 128 256), good := (rows 69 74 69 266 82 192 192 192 256) }] }

theorem u7148 : Upper (D 7) (R 7) [36,72,65,258,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7149 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 74, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 69 266 145 48 66 160 416), lower := (rows 37 74 69 266 145 48 66 128 256), losses := [] }

theorem u7149 : Upper (D 7) (R 7) [36,72,65,258,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7149 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7150 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 266 145 48 96 130 386), lower := (rows 37 74 69 266 145 48 96 128 256), losses := [] }

theorem u7150 : Upper (D 7) (R 7) [36,72,65,258,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7150 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7151 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 69 266 145 48 192 162 290), lower := (rows 37 74 69 266 145 48 192 128 256), losses := [] }

theorem u7151 : Upper (D 7) (R 7) [36,72,65,258,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7151 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 74, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 69 266 145 160 66 176 304), lower := (rows 37 74 69 266 145 160 66 128 256), losses := [] }

theorem u7152 : Upper (D 7) (R 7) [36,72,65,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 69 266 145 160 80 162 290), lower := (rows 37 74 69 266 145 160 80 128 256), losses := [] }

theorem u7153 : Upper (D 7) (R 7) [36,72,65,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7153 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7154 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 266 145 160 96 146 274), lower := (rows 37 74 69 266 145 160 96 128 256), losses := [] }

theorem u7154 : Upper (D 7) (R 7) [36,72,65,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7155 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 266 146 48 65 160 416), lower := (rows 37 74 69 266 146 48 65 128 256), losses := [] }

theorem u7155 : Upper (D 7) (R 7) [36,72,65,258,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7155 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7156 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 37 74 69 266 146 48 96 129 385), lower := (rows 37 74 69 266 146 48 96 128 256), losses := [] }

theorem u7156 : Upper (D 7) (R 7) [36,72,65,258,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7156 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 74 69 266 146 48 192 161 289), lower := (rows 37 74 69 266 146 48 192 128 256), losses := [{ target := 7, region := (rows 1 6 4 13 16 48 64 0 257), good := (rows 303 74 335 266 50 48 64 0 256) }] }

theorem u7157 : Upper (D 7) (R 7) [36,72,65,258,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7157 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7158 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 266 146 160 65 176 304), lower := (rows 37 74 69 266 146 160 65 128 256), losses := [] }

theorem u7158 : Upper (D 7) (R 7) [36,72,65,258,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7159 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 69 266 146 160 80 161 289), lower := (rows 37 74 69 266 146 160 80 128 256), losses := [] }

theorem u7159 : Upper (D 7) (R 7) [36,72,65,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7159 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7160 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 266 146 160 96 145 273), lower := (rows 37 74 69 266 146 160 96 128 256), losses := [] }

theorem u7160 : Upper (D 7) (R 7) [36,72,65,258,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7161 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 3, region := 66, targets := 160 }], pairs := [(0,1),(1,5),(1,7),(2,1)], upper := (rows 37 74 69 280 19 160 66 160 416), lower := (rows 37 74 69 280 19 160 66 128 256), losses := [] }

theorem u7161 : Upper (D 7) (R 7) [36,72,65,272,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7162 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 19 160 96 130 386), lower := (rows 37 74 69 280 19 160 96 128 256), losses := [] }

theorem u7162 : Upper (D 7) (R 7) [36,72,65,272,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7163 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 280 19 160 192 162 290), lower := (rows 37 74 69 280 19 160 192 128 256), losses := [] }

theorem u7163 : Upper (D 7) (R 7) [36,72,65,272,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7164 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 280 50 160 65 130 386), lower := (rows 37 74 69 280 50 160 65 128 256), losses := [] }

theorem u7164 : Upper (D 7) (R 7) [36,72,65,272,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7165 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 69 280 50 160 66 129 385), lower := (rows 37 74 69 280 50 160 66 128 256), losses := [] }

theorem u7165 : Upper (D 7) (R 7) [36,72,65,272,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7166 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(2,5),(4,0)], upper := (rows 37 74 69 280 50 160 192 131 259), lower := (rows 37 74 69 280 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 122 100 280 114 224 224 224 256) },{ target := 5, region := (rows 1 2 5 8 16 0 224 128 256), good := (rows 69 74 69 280 82 192 192 192 256) }] }

theorem u7166 : Upper (D 7) (R 7) [36,72,65,272,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7167 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 69 280 145 160 66 162 290), lower := (rows 37 74 69 280 145 160 66 128 256), losses := [] }

theorem u7167 : Upper (D 7) (R 7) [36,72,65,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7168 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 145 160 96 130 258), lower := (rows 37 74 69 280 145 160 96 128 256), losses := [] }

theorem u7168 : Upper (D 7) (R 7) [36,72,65,272,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7169 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 280 146 160 65 162 290), lower := (rows 37 74 69 280 146 160 65 128 256), losses := [] }

theorem u7169 : Upper (D 7) (R 7) [36,72,65,272,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7170 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 69 280 146 160 66 161 289), lower := (rows 37 74 69 280 146 160 66 128 256), losses := [] }

theorem u7170 : Upper (D 7) (R 7) [36,72,65,272,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7171 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 146 160 96 131 259), lower := (rows 37 74 69 280 146 160 96 128 256), losses := [] }

theorem u7171 : Upper (D 7) (R 7) [36,72,65,272,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7172 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 280 176 34 65 130 386), lower := (rows 37 74 69 280 176 34 65 128 256), losses := [] }

theorem u7172 : Upper (D 7) (R 7) [36,72,65,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7173 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 69 280 176 34 66 129 385), lower := (rows 37 74 69 280 176 34 66 128 256), losses := [] }

theorem u7173 : Upper (D 7) (R 7) [36,72,65,272,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7174 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 176 34 192 131 259), lower := (rows 37 74 69 280 176 34 192 128 256), losses := [] }

theorem u7174 : Upper (D 7) (R 7) [36,72,65,272,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7175 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 69 296 145 160 66 146 274), lower := (rows 37 74 69 296 145 160 66 128 256), losses := [] }

theorem u7175 : Upper (D 7) (R 7) [36,72,65,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7176 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 69 296 145 160 80 130 258), lower := (rows 37 74 69 296 145 160 80 128 256), losses := [] }

theorem u7176 : Upper (D 7) (R 7) [36,72,65,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7176 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7177 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 296 146 34 65 144 400), lower := (rows 37 74 69 296 146 34 65 128 256), losses := [] }

theorem u7177 : Upper (D 7) (R 7) [36,72,65,288,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7178 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 74 69 296 146 34 80 129 385), lower := (rows 37 74 69 296 146 34 80 128 256), losses := [] }

theorem u7178 : Upper (D 7) (R 7) [36,72,65,288,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7178 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7179 : Route 9 := (fun mask => (mask,id))

def c7179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7179 : Upper (D 7) (R 7) [36,72,65,288,130,2,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,130,2,128] 13 (by decide) (choices 1) [1,16] r7179 c7179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u522
  · exact u523

def b7180 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 296 146 48 65 130 386), lower := (rows 37 74 69 296 146 48 65 128 256), losses := [] }

theorem u7180 : Upper (D 7) (R 7) [36,72,65,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7181 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 296 146 48 66 129 385), lower := (rows 37 74 69 296 146 48 66 128 256), losses := [] }

theorem u7181 : Upper (D 7) (R 7) [36,72,65,288,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7181 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7182 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 74 69 296 146 48 192 131 259), lower := (rows 37 74 69 296 146 48 192 128 256), losses := [{ target := 7, region := (rows 1 6 4 9 16 48 64 0 261), good := (rows 303 74 335 296 50 48 64 0 256) }] }

theorem u7182 : Upper (D 7) (R 7) [36,72,65,288,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7182 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7183 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 296 146 160 65 146 274), lower := (rows 37 74 69 296 146 160 65 128 256), losses := [] }

theorem u7183 : Upper (D 7) (R 7) [36,72,65,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7184 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 69 296 146 160 66 145 273), lower := (rows 37 74 69 296 146 160 66 128 256), losses := [] }

theorem u7184 : Upper (D 7) (R 7) [36,72,65,288,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7185 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 74 69 296 146 160 80 131 259), lower := (rows 37 74 69 296 146 160 80 128 256), losses := [{ target := 7, region := (rows 1 6 4 9 16 32 80 0 261), good := (rows 303 74 335 296 82 32 80 0 256) }] }

theorem u7185 : Upper (D 7) (R 7) [36,72,65,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7185 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7186 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 69 392 145 48 66 162 290), lower := (rows 37 74 69 392 145 48 66 128 256), losses := [] }

theorem u7186 : Upper (D 7) (R 7) [36,72,65,384,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7186 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7187 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 392 145 48 96 130 258), lower := (rows 37 74 69 392 145 48 96 128 256), losses := [] }

theorem u7187 : Upper (D 7) (R 7) [36,72,65,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7187 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7188 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 392 146 34 65 176 304), lower := (rows 37 74 69 392 146 34 65 128 256), losses := [] }

theorem u7188 : Upper (D 7) (R 7) [36,72,65,384,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7189 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 74 69 392 146 34 80 161 289), lower := (rows 37 74 69 392 146 34 80 128 256), losses := [] }

theorem u7189 : Upper (D 7) (R 7) [36,72,65,384,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7189 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7190 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 392 146 34 96 145 273), lower := (rows 37 74 69 392 146 34 96 128 256), losses := [] }

theorem u7190 : Upper (D 7) (R 7) [36,72,65,384,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7191 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 392 146 48 65 162 290), lower := (rows 37 74 69 392 146 48 65 128 256), losses := [] }

theorem u7191 : Upper (D 7) (R 7) [36,72,65,384,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7191 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7192 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 74 69 392 146 48 66 161 289), lower := (rows 37 74 69 392 146 48 66 128 256), losses := [] }

theorem u7192 : Upper (D 7) (R 7) [36,72,65,384,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7192 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 392 146 48 96 131 259), lower := (rows 37 74 69 392 146 48 96 128 256), losses := [] }

theorem u7193 : Upper (D 7) (R 7) [36,72,65,384,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7193 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7194 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 392 176 34 65 146 274), lower := (rows 37 74 69 392 176 34 65 128 256), losses := [] }

theorem u7194 : Upper (D 7) (R 7) [36,72,65,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7195 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 69 392 176 34 66 145 273), lower := (rows 37 74 69 392 176 34 66 128 256), losses := [] }

theorem u7195 : Upper (D 7) (R 7) [36,72,65,384,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7196 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 392 176 34 80 131 259), lower := (rows 37 74 69 392 176 34 80 128 256), losses := [] }

theorem u7196 : Upper (D 7) (R 7) [36,72,65,384,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7196 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7197 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 84 137 50 288 65 130 386), lower := (rows 37 74 84 137 50 288 65 128 256), losses := [] }

theorem u7197 : Upper (D 7) (R 7) [36,72,80,129,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7197 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7198 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 74 84 137 50 288 66 129 385), lower := (rows 37 74 84 137 50 288 66 128 256), losses := [] }

theorem u7198 : Upper (D 7) (R 7) [36,72,80,129,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7198 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7199 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 84 137 50 288 192 131 259), lower := (rows 37 74 84 137 50 288 192 128 256), losses := [] }

theorem u7199 : Upper (D 7) (R 7) [36,72,80,129,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7199 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P07
