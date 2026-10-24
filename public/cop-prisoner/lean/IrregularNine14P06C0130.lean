import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7800 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 6 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(3,2)], upper := (rows 35 194 268 104 22 36 65 145 273), lower := (rows 35 194 268 104 22 36 65 128 256), losses := [] }

theorem u7800 : Upper (D 6) (R 6) [34,192,264,96,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7801 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 268 104 22 36 80 129 257), lower := (rows 35 194 268 104 22 36 80 128 256), losses := [] }

theorem u7801 : Upper (D 6) (R 6) [34,192,264,96,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7801 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7802 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 292 14 84 33 65 152 280), lower := (rows 35 194 292 14 84 33 65 128 256), losses := [] }

theorem u7802 : Upper (D 6) (R 6) [34,192,288,6,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7803 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 292 14 84 33 72 145 273), lower := (rows 35 194 292 14 84 33 72 128 256), losses := [] }

theorem u7803 : Upper (D 6) (R 6) [34,192,288,6,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7803 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7804 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 292 14 84 33 80 137 265), lower := (rows 35 194 292 14 84 33 80 128 256), losses := [] }

theorem u7804 : Upper (D 6) (R 6) [34,192,288,6,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7804 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7805 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 292, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 35 194 292 25 84 33 66 140 268), lower := (rows 35 194 292 25 84 33 66 128 256), losses := [] }

theorem u7805 : Upper (D 6) (R 6) [34,192,288,17,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7806 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 292 25 84 33 68 138 266), lower := (rows 35 194 292 25 84 33 68 128 256), losses := [] }

theorem u7806 : Upper (D 6) (R 6) [34,192,288,17,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7807 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 292 25 84 33 72 134 262), lower := (rows 35 194 292 25 84 33 72 128 256), losses := [] }

theorem u7807 : Upper (D 6) (R 6) [34,192,288,17,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7807 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7808 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 292 25 84 40 65 134 262), lower := (rows 35 194 292 25 84 40 65 128 256), losses := [] }

theorem u7808 : Upper (D 6) (R 6) [34,192,288,17,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7808 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7809 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 292 25 84 40 66 133 261), lower := (rows 35 194 292 25 84 40 66 128 256), losses := [] }

theorem u7809 : Upper (D 6) (R 6) [34,192,288,17,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7809 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7810 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 292 25 84 40 68 131 259), lower := (rows 35 194 292 25 84 40 68 128 256), losses := [] }

theorem u7810 : Upper (D 6) (R 6) [34,192,288,17,68,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7810 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7811 : Route 9 := (fun mask => (mask,id))

def c7811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7811 : Upper (D 6) (R 6) [34,192,320,5,10,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,10,4,1] 13 (by decide) (choices 1) [16,32] r7811 c7811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u607
  · exact u608

def b7812 : PairBound 9 := { available := 33, camps := [], pairs := [(1,2),(2,1)], upper := (rows 35 194 324 13 26 36 80 161 289), lower := (rows 35 194 324 13 26 36 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 124 80 137 265), good := (rows 417 224 356 429 508 36 116 128 256) },{ target := 2, region := (rows 1 10 0 8 24 32 88 129 257), good := (rows 419 194 320 475 90 32 80 128 256) }] }

theorem u7812 : Upper (D 6) (R 6) [34,192,320,5,10,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7812 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7813 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 35 194 324 13 26 36 96 145 273), lower := (rows 35 194 324 13 26 36 96 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 24 32 97 136 264), good := (rows 99 194 320 475 410 96 96 128 256) }] }

theorem u7813 : Upper (D 6) (R 6) [34,192,320,5,10,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7814 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 35 194 324 25 28 36 65 162 290), lower := (rows 35 194 324 25 28 36 65 128 256), losses := [] }

theorem u7814 : Upper (D 6) (R 6) [34,192,320,17,12,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7815 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 324 25 28 36 66 161 289), lower := (rows 35 194 324 25 28 36 66 128 256), losses := [] }

theorem u7815 : Upper (D 6) (R 6) [34,192,320,17,12,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7816 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 194 324 25 28 36 96 131 259), lower := (rows 35 194 324 25 28 36 96 128 256), losses := [] }

theorem u7816 : Upper (D 6) (R 6) [34,192,320,17,12,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7817 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 324 26 52 33 65 140 268), lower := (rows 35 194 324 26 52 33 65 128 256), losses := [] }

theorem u7817 : Upper (D 6) (R 6) [34,192,320,18,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7818 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 324 26 52 33 68 137 265), lower := (rows 35 194 324 26 52 33 68 128 256), losses := [] }

theorem u7818 : Upper (D 6) (R 6) [34,192,320,18,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7819 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 324 26 52 33 72 133 261), lower := (rows 35 194 324 26 52 33 72 128 256), losses := [] }

theorem u7819 : Upper (D 6) (R 6) [34,192,320,18,36,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7819 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7820 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 76 82 33 65 148 276), lower := (rows 35 386 44 76 82 33 65 128 256), losses := [] }

theorem u7820 : Upper (D 6) (R 6) [34,384,40,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7821 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 44 76 82 33 68 145 273), lower := (rows 35 386 44 76 82 33 68 128 256), losses := [] }

theorem u7821 : Upper (D 6) (R 6) [34,384,40,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7822 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 386 44 76 82 33 80 133 261), lower := (rows 35 386 44 76 82 33 80 128 256), losses := [] }

theorem u7822 : Upper (D 6) (R 6) [34,384,40,68,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7822 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7823 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 70 25 28 33 96 196 324), lower := (rows 35 386 70 25 28 33 96 128 256), losses := [] }

theorem u7823 : Upper (D 6) (R 6) [34,384,66,17,12,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7824 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 25 28 36 96 193 321), lower := (rows 35 386 70 25 28 36 96 128 256), losses := [] }

theorem u7824 : Upper (D 6) (R 6) [34,384,66,17,12,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 386 70 25 28 96 96 133 261), lower := (rows 35 386 70 25 28 96 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 511 511 128 256), good := (rows 102 486 102 124 124 96 96 224 352) }] }

theorem u7825 : Upper (D 6) (R 6) [34,384,66,17,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7826 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 70 25 88 36 65 164 292), lower := (rows 35 386 70 25 88 36 65 128 256), losses := [] }

theorem u7826 : Upper (D 6) (R 6) [34,384,66,17,72,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7827 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 70 25 88 36 68 161 289), lower := (rows 35 386 70 25 88 36 68 128 256), losses := [] }

theorem u7827 : Upper (D 6) (R 6) [34,384,66,17,72,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7828 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 386 70 25 88 36 96 133 261), lower := (rows 35 386 70 25 88 36 96 128 256), losses := [] }

theorem u7828 : Upper (D 6) (R 6) [34,384,66,17,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7829 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 386 76 13 22 96 65 176 304), lower := (rows 35 386 76 13 22 96 65 128 256), losses := [] }

theorem u7829 : Upper (D 6) (R 6) [34,384,72,5,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7830 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 386 76 13 22 96 80 161 289), lower := (rows 35 386 76 13 22 96 80 128 256), losses := [] }

theorem u7830 : Upper (D 6) (R 6) [34,384,72,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7830 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7831 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 386 76 13 22 96 96 145 273), lower := (rows 35 386 76 13 22 96 96 128 256), losses := [] }

theorem u7831 : Upper (D 6) (R 6) [34,384,72,5,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7832 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 76 13 82 33 68 176 304), lower := (rows 35 386 76 13 82 33 68 128 256), losses := [] }

theorem u7832 : Upper (D 6) (R 6) [34,384,72,5,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7833 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 386 76 13 82 33 80 164 292), lower := (rows 35 386 76 13 82 33 80 128 256), losses := [] }

theorem u7833 : Upper (D 6) (R 6) [34,384,72,5,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7833 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7834 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 76 13 82 33 96 148 276), lower := (rows 35 386 76 13 82 33 96 128 256), losses := [] }

theorem u7834 : Upper (D 6) (R 6) [34,384,72,5,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7835 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 386 76 14 21 96 65 176 304), lower := (rows 35 386 76 14 21 96 65 128 256), losses := [] }

theorem u7835 : Upper (D 6) (R 6) [34,384,72,6,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7836 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 386 76 14 21 96 80 161 289), lower := (rows 35 386 76 14 21 96 80 128 256), losses := [] }

theorem u7836 : Upper (D 6) (R 6) [34,384,72,6,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7836 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7837 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 386 76 14 21 96 96 145 273), lower := (rows 35 386 76 14 21 96 96 128 256), losses := [] }

theorem u7837 : Upper (D 6) (R 6) [34,384,72,6,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7838 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 386 76 26 21 96 65 164 292), lower := (rows 35 386 76 26 21 96 65 128 256), losses := [] }

theorem u7838 : Upper (D 6) (R 6) [34,384,72,18,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7839 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 76 26 21 96 68 161 289), lower := (rows 35 386 76 26 21 96 68 128 256), losses := [] }

theorem u7839 : Upper (D 6) (R 6) [34,384,72,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7840 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 386 76 26 21 96 96 133 261), lower := (rows 35 386 76 26 21 96 96 128 256), losses := [] }

theorem u7840 : Upper (D 6) (R 6) [34,384,72,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7841 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 76 44 82 33 65 148 276), lower := (rows 35 386 76 44 82 33 65 128 256), losses := [] }

theorem u7841 : Upper (D 6) (R 6) [34,384,72,36,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7842 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 76 44 82 33 68 145 273), lower := (rows 35 386 76 44 82 33 68 128 256), losses := [] }

theorem u7842 : Upper (D 6) (R 6) [34,384,72,36,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7843 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 386 76 44 82 33 80 133 261), lower := (rows 35 386 76 44 82 33 80 128 256), losses := [] }

theorem u7843 : Upper (D 6) (R 6) [34,384,72,36,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7843 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7844 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 386 100 14 88 33 65 148 276), lower := (rows 35 386 100 14 88 33 65 128 256), losses := [] }

theorem u7844 : Upper (D 6) (R 6) [34,384,96,6,72,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7845 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 100 14 88 33 68 145 273), lower := (rows 35 386 100 14 88 33 68 128 256), losses := [] }

theorem u7845 : Upper (D 6) (R 6) [34,384,96,6,72,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7846 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 386 100 14 88 33 80 133 261), lower := (rows 35 386 100 14 88 33 80 128 256), losses := [] }

theorem u7846 : Upper (D 6) (R 6) [34,384,96,6,72,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7846 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7847 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 386 100 25 82 36 65 140 268), lower := (rows 35 386 100 25 82 36 65 128 256), losses := [] }

theorem u7847 : Upper (D 6) (R 6) [34,384,96,17,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7848 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 386 100 25 82 36 68 137 265), lower := (rows 35 386 100 25 82 36 68 128 256), losses := [] }

theorem u7848 : Upper (D 6) (R 6) [34,384,96,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7849 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 386 100 25 82 36 72 133 261), lower := (rows 35 386 100 25 82 36 72 128 256), losses := [] }

theorem u7849 : Upper (D 6) (R 6) [34,384,96,17,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7849 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7850 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 386 100 26 81 36 65 140 268), lower := (rows 35 386 100 26 81 36 65 128 256), losses := [] }

theorem u7850 : Upper (D 6) (R 6) [34,384,96,18,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7851 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 394, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 386 100 26 81 36 68 137 265), lower := (rows 35 386 100 26 81 36 68 128 256), losses := [] }

theorem u7851 : Upper (D 6) (R 6) [34,384,96,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7852 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 386 100 26 81 36 72 133 261), lower := (rows 35 386 100 26 81 36 72 128 256), losses := [] }

theorem u7852 : Upper (D 6) (R 6) [34,384,96,18,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7852 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7853 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 41 50 133 14 84 288 65 194 322), lower := (rows 41 50 133 14 84 288 65 128 256), losses := [] }

theorem u7853 : Upper (D 6) (R 6) [40,48,129,6,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7853 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7854 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 41 50 133 14 84 288 66 193 321), lower := (rows 41 50 133 14 84 288 66 128 256), losses := [] }

theorem u7854 : Upper (D 6) (R 6) [40,48,129,6,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7854 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7855 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 97, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 41 50 133 14 276 96 65 194 322), lower := (rows 41 50 133 14 276 96 65 128 256), losses := [{ target := 2, region := (rows 9 18 0 8 16 125 77 152 280), good := (rows 489 434 225 491 498 96 97 128 256) }] }

theorem u7855 : Upper (D 6) (R 6) [40,48,129,6,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7856 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 41 50 133 14 276 96 66 193 321), lower := (rows 41 50 133 14 276 96 66 128 256), losses := [] }

theorem u7856 : Upper (D 6) (R 6) [40,48,129,6,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7857 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 173, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 73 274 36 66 196 324), lower := (rows 41 50 133 73 274 36 66 128 256), losses := [] }

theorem u7857 : Upper (D 6) (R 6) [40,48,129,65,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7858 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 73 274 36 68 194 322), lower := (rows 41 50 133 73 274 36 68 128 256), losses := [] }

theorem u7858 : Upper (D 6) (R 6) [40,48,129,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7859 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 73 336 36 66 134 262), lower := (rows 41 50 133 73 336 36 66 128 256), losses := [] }

theorem u7859 : Upper (D 6) (R 6) [40,48,129,65,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7859
end Delivery.IrregularNine14.P06
