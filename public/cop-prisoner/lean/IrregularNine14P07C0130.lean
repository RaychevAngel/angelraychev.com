import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7800 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 392 146 34 80 129 257), lower := (rows 37 98 76 392 146 34 80 128 256), losses := [] }

theorem u7800 : Upper (D 7) (R 7) [36,96,72,384,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7800 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7801 : Route 9 := (fun mask => (mask,id))

def c7801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7801 : Upper (D 7) (R 7) [36,96,72,384,130,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,130,16,1] 13 (by decide) (choices 1) [1,2] r7801 c7801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u604
  · exact u605

def b7802 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 392 146 48 66 129 257), lower := (rows 37 98 76 392 146 48 66 128 256), losses := [] }

theorem u7802 : Upper (D 7) (R 7) [36,96,72,384,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7802 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7803 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 25 208 34 66 392 264), lower := (rows 37 98 133 25 208 34 66 128 256), losses := [] }

theorem u7803 : Upper (D 7) (R 7) [36,96,129,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7804 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 37 98 133 25 208 34 72 386 258), lower := (rows 37 98 133 25 208 34 72 128 256), losses := [] }

theorem u7804 : Upper (D 7) (R 7) [36,96,129,17,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7804 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7805 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 25 208 34 320 138 266), lower := (rows 37 98 133 25 208 34 320 128 256), losses := [] }

theorem u7805 : Upper (D 7) (R 7) [36,96,129,17,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7805 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7806 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 25 336 34 66 136 392), lower := (rows 37 98 133 25 336 34 66 128 256), losses := [] }

theorem u7806 : Upper (D 7) (R 7) [36,96,129,17,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7807 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 133 25 336 34 72 130 386), lower := (rows 37 98 133 25 336 34 72 128 256), losses := [] }

theorem u7807 : Upper (D 7) (R 7) [36,96,129,17,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7807 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7808 : Route 9 := (fun mask => (mask,id))

def c7808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7808 : Upper (D 7) (R 7) [36,96,129,17,320,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,320,2,128] 13 (by decide) (choices 1) [2,8] r7808 c7808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u606
  · exact u607

def b7809 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 25 400 34 66 200 328), lower := (rows 37 98 133 25 400 34 66 128 256), losses := [] }

theorem u7809 : Upper (D 7) (R 7) [36,96,129,17,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7810 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 133 25 400 34 72 194 322), lower := (rows 37 98 133 25 400 34 72 128 256), losses := [] }

theorem u7810 : Upper (D 7) (R 7) [36,96,129,17,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7810 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7811 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 26 152 288 65 194 322), lower := (rows 37 98 133 26 152 288 65 128 256), losses := [] }

theorem u7811 : Upper (D 7) (R 7) [36,96,129,18,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7811 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7812 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 98 133 26 152 288 66 193 321), lower := (rows 37 98 133 26 152 288 66 128 256), losses := [] }

theorem u7812 : Upper (D 7) (R 7) [36,96,129,18,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7812 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7813 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 26 208 288 65 138 266), lower := (rows 37 98 133 26 208 288 65 128 256), losses := [] }

theorem u7813 : Upper (D 7) (R 7) [36,96,129,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7813 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7814 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 26 208 288 66 137 265), lower := (rows 37 98 133 26 208 288 66 128 256), losses := [] }

theorem u7814 : Upper (D 7) (R 7) [36,96,129,18,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7814 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7815 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 133 26 208 288 72 131 259), lower := (rows 37 98 133 26 208 288 72 128 256), losses := [] }

theorem u7815 : Upper (D 7) (R 7) [36,96,129,18,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7815 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7816 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 133 26 273 34 72 192 448), lower := (rows 37 98 133 26 273 34 72 128 256), losses := [] }

theorem u7816 : Upper (D 7) (R 7) [36,96,129,18,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7816 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7817 : Route 9 := (fun mask => (mask,id))

def c7817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7817 : Upper (D 7) (R 7) [36,96,129,18,257,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,257,2,128] 13 (by decide) (choices 1) [8,64] r7817 c7817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u608
  · exact u609

def b7818 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 133 26 273 40 66 192 448), lower := (rows 37 98 133 26 273 40 66 128 256), losses := [] }

theorem u7818 : Upper (D 7) (R 7) [36,96,129,18,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7818 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7819 : Route 9 := (fun mask => (mask,id))

def c7819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7819 : Upper (D 7) (R 7) [36,96,129,18,257,8,128] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,257,8,128] 13 (by decide) (choices 1) [2,64] r7819 c7819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u610
  · exact u611

def b7820 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 26 400 34 65 200 328), lower := (rows 37 98 133 26 400 34 65 128 256), losses := [] }

theorem u7820 : Upper (D 7) (R 7) [36,96,129,18,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7821 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 26 400 34 72 193 321), lower := (rows 37 98 133 26 400 34 72 128 256), losses := [] }

theorem u7821 : Upper (D 7) (R 7) [36,96,129,18,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7821 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7822 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 26 400 40 65 194 322), lower := (rows 37 98 133 26 400 40 65 128 256), losses := [] }

theorem u7822 : Upper (D 7) (R 7) [36,96,129,18,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7822 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7823 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 26 400 40 66 193 321), lower := (rows 37 98 133 26 400 40 66 128 256), losses := [] }

theorem u7823 : Upper (D 7) (R 7) [36,96,129,18,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7823 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7824 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 133 73 146 288 66 152 280), lower := (rows 37 98 133 73 146 288 66 128 256), losses := [] }

theorem u7824 : Upper (D 7) (R 7) [36,96,129,65,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7824 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 133 73 146 288 72 146 274), lower := (rows 37 98 133 73 146 288 72 128 256), losses := [] }

theorem u7825 : Upper (D 7) (R 7) [36,96,129,65,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7825 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7826 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 37 98 133 73 146 288 80 138 266), lower := (rows 37 98 133 73 146 288 80 128 256), losses := [] }

theorem u7826 : Upper (D 7) (R 7) [36,96,129,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7826 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7827 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 133 73 152 34 66 400 272), lower := (rows 37 98 133 73 152 34 66 128 256), losses := [] }

theorem u7827 : Upper (D 7) (R 7) [36,96,129,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7828 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 37 98 133 73 152 34 80 386 258), lower := (rows 37 98 133 73 152 34 80 128 256), losses := [] }

theorem u7828 : Upper (D 7) (R 7) [36,96,129,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7828 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7829 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 73 152 34 320 146 274), lower := (rows 37 98 133 73 152 34 320 128 256), losses := [] }

theorem u7829 : Upper (D 7) (R 7) [36,96,129,65,136,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7829 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7830 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 73 274 34 72 144 400), lower := (rows 37 98 133 73 274 34 72 128 256), losses := [] }

theorem u7830 : Upper (D 7) (R 7) [36,96,129,65,258,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7830 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7831 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 73 274 34 80 136 392), lower := (rows 37 98 133 73 274 34 80 128 256), losses := [] }

theorem u7831 : Upper (D 7) (R 7) [36,96,129,65,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7831 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7832 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,0)], upper := (rows 37 98 133 73 274 34 192 152 280), lower := (rows 37 98 133 73 274 34 192 128 256), losses := [] }

theorem u7832 : Upper (D 7) (R 7) [36,96,129,65,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7833 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 73 274 48 66 136 392), lower := (rows 37 98 133 73 274 48 66 128 256), losses := [] }

theorem u7833 : Upper (D 7) (R 7) [36,96,129,65,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7833 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7834 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 133 73 274 48 72 130 386), lower := (rows 37 98 133 73 274 48 72 128 256), losses := [] }

theorem u7834 : Upper (D 7) (R 7) [36,96,129,65,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7834 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7835 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 37 98 133 73 274 48 192 138 266), lower := (rows 37 98 133 73 274 48 192 128 256), losses := [] }

theorem u7835 : Upper (D 7) (R 7) [36,96,129,65,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7835 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7836 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 133 73 280 34 66 144 400), lower := (rows 37 98 133 73 280 34 66 128 256), losses := [] }

theorem u7836 : Upper (D 7) (R 7) [36,96,129,65,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7837 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 133 73 280 34 80 130 386), lower := (rows 37 98 133 73 280 34 80 128 256), losses := [] }

theorem u7837 : Upper (D 7) (R 7) [36,96,129,65,264,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7837 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7838 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,0)], upper := (rows 37 98 133 73 280 34 192 146 274), lower := (rows 37 98 133 73 280 34 192 128 256), losses := [] }

theorem u7838 : Upper (D 7) (R 7) [36,96,129,65,264,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7839 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 133 73 400 34 66 152 280), lower := (rows 37 98 133 73 400 34 66 128 256), losses := [] }

theorem u7839 : Upper (D 7) (R 7) [36,96,129,65,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7840 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 73 400 34 72 146 274), lower := (rows 37 98 133 73 400 34 72 128 256), losses := [] }

theorem u7840 : Upper (D 7) (R 7) [36,96,129,65,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7840 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7841 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 73 400 34 80 138 266), lower := (rows 37 98 133 73 400 34 80 128 256), losses := [] }

theorem u7841 : Upper (D 7) (R 7) [36,96,129,65,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7841 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7842 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 88 146 288 65 138 266), lower := (rows 37 98 133 88 146 288 65 128 256), losses := [] }

theorem u7842 : Upper (D 7) (R 7) [36,96,129,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7842 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7843 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 88 146 288 66 137 265), lower := (rows 37 98 133 88 146 288 66 128 256), losses := [] }

theorem u7843 : Upper (D 7) (R 7) [36,96,129,80,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7843 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7844 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 37 98 133 88 146 288 72 131 259), lower := (rows 37 98 133 88 146 288 72 128 256), losses := [] }

theorem u7844 : Upper (D 7) (R 7) [36,96,129,80,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7844 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7845 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 88 273 34 66 136 392), lower := (rows 37 98 133 88 273 34 66 128 256), losses := [] }

theorem u7845 : Upper (D 7) (R 7) [36,96,129,80,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7846 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 88 273 34 72 130 386), lower := (rows 37 98 133 88 273 34 72 128 256), losses := [] }

theorem u7846 : Upper (D 7) (R 7) [36,96,129,80,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7846 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7847 : Route 9 := (fun mask => (mask,id))

def c7847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7847 : Upper (D 7) (R 7) [36,96,129,80,257,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,257,2,128] 13 (by decide) (choices 1) [2,8] r7847 c7847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u612
  · exact u613

def b7848 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 88 400 34 65 138 266), lower := (rows 37 98 133 88 400 34 65 128 256), losses := [] }

theorem u7848 : Upper (D 7) (R 7) [36,96,129,80,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7849 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 88 400 34 66 137 265), lower := (rows 37 98 133 88 400 34 66 128 256), losses := [] }

theorem u7849 : Upper (D 7) (R 7) [36,96,129,80,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7850 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 88 400 34 72 131 259), lower := (rows 37 98 133 88 400 34 72 128 256), losses := [] }

theorem u7850 : Upper (D 7) (R 7) [36,96,129,80,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7850 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7851 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 138 274 48 65 200 328), lower := (rows 37 98 133 138 274 48 65 128 256), losses := [] }

theorem u7851 : Upper (D 7) (R 7) [36,96,129,130,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7851 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7852 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 98 133 138 274 48 72 193 321), lower := (rows 37 98 133 138 274 48 72 128 256), losses := [] }

theorem u7852 : Upper (D 7) (R 7) [36,96,129,130,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7852 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7853 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 138 280 48 65 194 322), lower := (rows 37 98 133 138 280 48 65 128 256), losses := [] }

theorem u7853 : Upper (D 7) (R 7) [36,96,129,130,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7853 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7854 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 98 133 138 280 48 66 193 321), lower := (rows 37 98 133 138 280 48 66 128 256), losses := [] }

theorem u7854 : Upper (D 7) (R 7) [36,96,129,130,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7854 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7855 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 152 273 34 66 200 328), lower := (rows 37 98 133 152 273 34 66 128 256), losses := [] }

theorem u7855 : Upper (D 7) (R 7) [36,96,129,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7856 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 152 273 34 72 194 322), lower := (rows 37 98 133 152 273 34 72 128 256), losses := [] }

theorem u7856 : Upper (D 7) (R 7) [36,96,129,144,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7856 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7857 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 152 280 34 65 194 322), lower := (rows 37 98 133 152 280 34 65 128 256), losses := [] }

theorem u7857 : Upper (D 7) (R 7) [36,96,129,144,264,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7858 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 152 280 34 66 193 321), lower := (rows 37 98 133 152 280 34 66 128 256), losses := [] }

theorem u7858 : Upper (D 7) (R 7) [36,96,129,144,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7859 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 152 336 34 65 138 266), lower := (rows 37 98 133 152 336 34 65 128 256), losses := [] }

theorem u7859 : Upper (D 7) (R 7) [36,96,129,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7859
end Delivery.IrregularNine14.P07
