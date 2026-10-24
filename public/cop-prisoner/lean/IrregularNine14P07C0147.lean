import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8820 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 37 194 261 11 112 160 72 146 274), lower := (rows 37 194 261 11 112 160 72 128 256), losses := [] }

theorem u8820 : Upper (D 7) (R 7) [36,192,257,3,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8820 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8821 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 194 261 11 112 160 80 138 266), lower := (rows 37 194 261 11 112 160 80 128 256), losses := [] }

theorem u8821 : Upper (D 7) (R 7) [36,192,257,3,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8821 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8822 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 261 25 26 96 66 160 416), lower := (rows 37 194 261 25 26 96 66 128 256), losses := [] }

theorem u8822 : Upper (D 7) (R 7) [36,192,257,17,10,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8823 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 261 25 26 96 96 130 386), lower := (rows 37 194 261 25 26 96 96 128 256), losses := [] }

theorem u8823 : Upper (D 7) (R 7) [36,192,257,17,10,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8824 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 261 25 26 96 192 162 290), lower := (rows 37 194 261 25 26 96 192 128 256), losses := [] }

theorem u8824 : Upper (D 7) (R 7) [36,192,257,17,10,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8825 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 261 56 81 34 66 136 392), lower := (rows 37 194 261 56 81 34 66 128 256), losses := [] }

theorem u8825 : Upper (D 7) (R 7) [36,192,257,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8826 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 194 261 56 81 34 72 130 386), lower := (rows 37 194 261 56 81 34 72 128 256), losses := [] }

theorem u8826 : Upper (D 7) (R 7) [36,192,257,48,65,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8826 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8827 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 261 56 81 34 192 138 266), lower := (rows 37 194 261 56 81 34 192 128 256), losses := [] }

theorem u8827 : Upper (D 7) (R 7) [36,192,257,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8828 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 170, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 194 261 56 81 160 66 138 266), lower := (rows 37 194 261 56 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 170 4 8 21 0 235 136 264), good := (rows 87 194 341 474 81 194 66 194 256) }] }

theorem u8828 : Upper (D 7) (R 7) [36,192,257,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8829 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 194 261 56 81 160 72 130 258), lower := (rows 37 194 261 56 81 160 72 128 256), losses := [] }

theorem u8829 : Upper (D 7) (R 7) [36,192,257,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8829 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8830 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,5),(4,0)], upper := (rows 37 194 261 73 152 34 66 176 304), lower := (rows 37 194 261 73 152 34 66 128 256), losses := [{ target := 5, region := (rows 1 146 4 9 16 0 242 128 256), good := (rows 77 194 269 73 218 66 66 194 256) }] }

theorem u8830 : Upper (D 7) (R 7) [36,192,257,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8831 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 261 73 152 34 80 162 290), lower := (rows 37 194 261 73 152 34 80 128 256), losses := [] }

theorem u8831 : Upper (D 7) (R 7) [36,192,257,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8831 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8832 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 261 73 152 34 96 146 274), lower := (rows 37 194 261 73 152 34 96 128 256), losses := [] }

theorem u8832 : Upper (D 7) (R 7) [36,192,257,65,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8833 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 261 73 152 48 66 162 290), lower := (rows 37 194 261 73 152 48 66 128 256), losses := [] }

theorem u8833 : Upper (D 7) (R 7) [36,192,257,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8833 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 261 73 152 48 96 130 258), lower := (rows 37 194 261 73 152 48 96 128 256), losses := [] }

theorem u8834 : Upper (D 7) (R 7) [36,192,257,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8834 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8835 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 1, region := 48, targets := 64 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,6)], upper := (rows 37 194 261 73 176 34 66 152 280), lower := (rows 37 194 261 73 176 34 66 128 256), losses := [] }

theorem u8835 : Upper (D 7) (R 7) [36,192,257,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8836 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 261 73 176 34 72 146 274), lower := (rows 37 194 261 73 176 34 72 128 256), losses := [] }

theorem u8836 : Upper (D 7) (R 7) [36,192,257,65,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8836 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8837 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 261 73 176 34 80 138 266), lower := (rows 37 194 261 73 176 34 80 128 256), losses := [] }

theorem u8837 : Upper (D 7) (R 7) [36,192,257,65,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8837 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8838 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 186, targets := 1 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 37 194 261 88 176 34 65 138 266), lower := (rows 37 194 261 88 176 34 65 128 256), losses := [] }

theorem u8838 : Upper (D 7) (R 7) [36,192,257,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8839 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 122, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,0)], upper := (rows 37 194 261 88 176 34 66 137 265), lower := (rows 37 194 261 88 176 34 66 128 256), losses := [] }

theorem u8839 : Upper (D 7) (R 7) [36,192,257,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8840 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 194 261 88 176 34 72 131 259), lower := (rows 37 194 261 88 176 34 72 128 256), losses := [] }

theorem u8840 : Upper (D 7) (R 7) [36,192,257,80,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8840 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8841 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 37 194 262 11 81 48 72 160 416), lower := (rows 37 194 262 11 81 48 72 128 256), losses := [] }

theorem u8841 : Upper (D 7) (R 7) [36,192,258,3,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8841 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8842 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 194 262 11 81 48 96 136 392), lower := (rows 37 194 262 11 81 48 96 128 256), losses := [] }

theorem u8842 : Upper (D 7) (R 7) [36,192,258,3,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8842 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8843 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 262 11 81 48 192 168 296), lower := (rows 37 194 262 11 81 48 192 128 256), losses := [] }

theorem u8843 : Upper (D 7) (R 7) [36,192,258,3,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8843 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8844 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 88, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 37 194 262 25 88 160 65 162 290), lower := (rows 37 194 262 25 88 160 65 128 256), losses := [] }

theorem u8844 : Upper (D 7) (R 7) [36,192,258,17,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8845 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 2, region := 161, targets := 2 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(2,6)], upper := (rows 37 194 262 25 88 160 66 161 289), lower := (rows 37 194 262 25 88 160 66 128 256), losses := [] }

theorem u8845 : Upper (D 7) (R 7) [36,192,258,17,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8846 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 194 262 25 88 160 96 131 259), lower := (rows 37 194 262 25 88 160 96 128 256), losses := [] }

theorem u8846 : Upper (D 7) (R 7) [36,192,258,17,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8847 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 121, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 194 262 25 112 40 65 130 386), lower := (rows 37 194 262 25 112 40 65 128 256), losses := [] }

theorem u8847 : Upper (D 7) (R 7) [36,192,258,17,96,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8847 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8848 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 194 262 25 112 40 66 129 385), lower := (rows 37 194 262 25 112 40 66 128 256), losses := [] }

theorem u8848 : Upper (D 7) (R 7) [36,192,258,17,96,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8848 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8849 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 262 25 112 40 192 131 259), lower := (rows 37 194 262 25 112 40 192 128 256), losses := [] }

theorem u8849 : Upper (D 7) (R 7) [36,192,258,17,96,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8849 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8850 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 194 262 26 81 160 65 168 296), lower := (rows 37 194 262 26 81 160 65 128 256), losses := [] }

theorem u8850 : Upper (D 7) (R 7) [36,192,258,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8851 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 194 262 26 81 160 72 161 289), lower := (rows 37 194 262 26 81 160 72 128 256), losses := [] }

theorem u8851 : Upper (D 7) (R 7) [36,192,258,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8851 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8852 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 262 26 81 160 96 137 265), lower := (rows 37 194 262 26 81 160 96 128 256), losses := [] }

theorem u8852 : Upper (D 7) (R 7) [36,192,258,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8853 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 194 262 42 81 48 65 136 392), lower := (rows 37 194 262 42 81 48 65 128 256), losses := [] }

theorem u8853 : Upper (D 7) (R 7) [36,192,258,34,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8853 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8854 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 37 194 262 42 81 48 72 129 385), lower := (rows 37 194 262 42 81 48 72 128 256), losses := [] }

theorem u8854 : Upper (D 7) (R 7) [36,192,258,34,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8854 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8855 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 262 42 81 48 192 137 265), lower := (rows 37 194 262 42 81 48 192 128 256), losses := [] }

theorem u8855 : Upper (D 7) (R 7) [36,192,258,34,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8855 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8856 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 194 262 56 81 160 65 138 266), lower := (rows 37 194 262 56 81 160 65 128 256), losses := [] }

theorem u8856 : Upper (D 7) (R 7) [36,192,258,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8857 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 168, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,1),(3,6)], upper := (rows 37 194 262 56 81 160 66 137 265), lower := (rows 37 194 262 56 81 160 66 128 256), losses := [] }

theorem u8857 : Upper (D 7) (R 7) [36,192,258,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8858 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 194 262 56 81 160 72 131 259), lower := (rows 37 194 262 56 81 160 72 128 256), losses := [] }

theorem u8858 : Upper (D 7) (R 7) [36,192,258,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8858 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8859 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 262 73 145 40 66 176 304), lower := (rows 37 194 262 73 145 40 66 128 256), losses := [] }

theorem u8859 : Upper (D 7) (R 7) [36,192,258,65,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8859 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8860 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 262 73 145 40 80 162 290), lower := (rows 37 194 262 73 145 40 80 128 256), losses := [] }

theorem u8860 : Upper (D 7) (R 7) [36,192,258,65,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8860 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8861 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 194 262 73 145 40 96 146 274), lower := (rows 37 194 262 73 145 40 96 128 256), losses := [] }

theorem u8861 : Upper (D 7) (R 7) [36,192,258,65,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8861 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8862 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,7)], upper := (rows 37 194 262 73 152 33 66 176 304), lower := (rows 37 194 262 73 152 33 66 128 256), losses := [] }

theorem u8862 : Upper (D 7) (R 7) [36,192,258,65,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8863 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 262 73 152 33 80 162 290), lower := (rows 37 194 262 73 152 33 80 128 256), losses := [] }

theorem u8863 : Upper (D 7) (R 7) [36,192,258,65,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8863 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8864 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 262 73 152 33 96 146 274), lower := (rows 37 194 262 73 152 33 96 128 256), losses := [] }

theorem u8864 : Upper (D 7) (R 7) [36,192,258,65,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8865 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 262 73 152 48 65 162 290), lower := (rows 37 194 262 73 152 48 65 128 256), losses := [] }

theorem u8865 : Upper (D 7) (R 7) [36,192,258,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8865 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8866 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 176, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 37 194 262 73 152 48 66 161 289), lower := (rows 37 194 262 73 152 48 66 128 256), losses := [] }

theorem u8866 : Upper (D 7) (R 7) [36,192,258,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8867 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 262 73 152 48 96 131 259), lower := (rows 37 194 262 73 152 48 96 128 256), losses := [] }

theorem u8867 : Upper (D 7) (R 7) [36,192,258,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8867 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8868 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,7)], upper := (rows 37 194 262 73 176 33 66 152 280), lower := (rows 37 194 262 73 176 33 66 128 256), losses := [] }

theorem u8868 : Upper (D 7) (R 7) [36,192,258,65,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8869 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 194 262 73 176 33 72 146 274), lower := (rows 37 194 262 73 176 33 72 128 256), losses := [] }

theorem u8869 : Upper (D 7) (R 7) [36,192,258,65,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8869 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8870 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 262 73 176 33 80 138 266), lower := (rows 37 194 262 73 176 33 80 128 256), losses := [] }

theorem u8870 : Upper (D 7) (R 7) [36,192,258,65,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8870 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8871 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 194 262 73 176 40 65 146 274), lower := (rows 37 194 262 73 176 40 65 128 256), losses := [] }

theorem u8871 : Upper (D 7) (R 7) [36,192,258,65,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8871 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8872 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 262 73 176 40 66 145 273), lower := (rows 37 194 262 73 176 40 66 128 256), losses := [] }

theorem u8872 : Upper (D 7) (R 7) [36,192,258,65,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8872 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8873 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 262 73 176 40 80 131 259), lower := (rows 37 194 262 73 176 40 80 128 256), losses := [] }

theorem u8873 : Upper (D 7) (R 7) [36,192,258,65,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8873 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8874 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 262 88 176 33 65 138 266), lower := (rows 37 194 262 88 176 33 65 128 256), losses := [] }

theorem u8874 : Upper (D 7) (R 7) [36,192,258,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8875 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 262 88 176 33 66 137 265), lower := (rows 37 194 262 88 176 33 66 128 256), losses := [] }

theorem u8875 : Upper (D 7) (R 7) [36,192,258,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8876 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 262 88 176 33 72 131 259), lower := (rows 37 194 262 88 176 33 72 128 256), losses := [] }

theorem u8876 : Upper (D 7) (R 7) [36,192,258,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8876 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8877 : PairBound 9 := { available := 160, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 3, region := 80, targets := 32 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 37 194 268 11 81 48 66 160 416), lower := (rows 37 194 268 11 81 48 66 128 256), losses := [] }

theorem u8877 : Upper (D 7) (R 7) [36,192,264,3,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8877 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8878 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 194 268 11 81 48 96 130 386), lower := (rows 37 194 268 11 81 48 96 128 256), losses := [] }

theorem u8878 : Upper (D 7) (R 7) [36,192,264,3,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8878 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8879 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 268 11 81 48 192 162 290), lower := (rows 37 194 268 11 81 48 192 128 256), losses := [] }

theorem u8879 : Upper (D 7) (R 7) [36,192,264,3,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8879 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8879
end Delivery.IrregularNine14.P07
