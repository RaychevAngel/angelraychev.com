import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10800 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 38 74 145 36 80 136 392), lower := (rows 97 259 38 74 145 36 80 128 256), losses := [] }

theorem u10800 : Upper (D 7) (R 7) [96,257,34,66,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10800 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10801 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 74 145 36 192 152 280), lower := (rows 97 259 38 74 145 36 192 128 256), losses := [] }

theorem u10801 : Upper (D 7) (R 7) [96,257,34,66,129,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10801 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10802 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 259 38 74 145 40 80 132 388), lower := (rows 97 259 38 74 145 40 80 128 256), losses := [] }

theorem u10802 : Upper (D 7) (R 7) [96,257,34,66,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10802 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10803 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 74 145 40 192 148 276), lower := (rows 97 259 38 74 145 40 192 128 256), losses := [] }

theorem u10803 : Upper (D 7) (R 7) [96,257,34,66,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10803 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10804 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 74 145 48 192 140 268), lower := (rows 97 259 38 74 145 48 192 128 256), losses := [] }

theorem u10804 : Upper (D 7) (R 7) [96,257,34,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10805 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 180, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 97 259 38 74 148 160 65 152 280), lower := (rows 97 259 38 74 148 160 65 128 256), losses := [] }

theorem u10805 : Upper (D 7) (R 7) [96,257,34,66,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10806 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 74 148 160 72 145 273), lower := (rows 97 259 38 74 148 160 72 128 256), losses := [] }

theorem u10806 : Upper (D 7) (R 7) [96,257,34,66,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10806 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10807 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 74 148 160 80 137 265), lower := (rows 97 259 38 74 148 160 80 128 256), losses := [] }

theorem u10807 : Upper (D 7) (R 7) [96,257,34,66,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10807 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10808 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(3,0),(3,5)], upper := (rows 97 259 38 76 145 48 66 136 392), lower := (rows 97 259 38 76 145 48 66 128 256), losses := [] }

theorem u10808 : Upper (D 7) (R 7) [96,257,34,68,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10808 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10809 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7)], upper := (rows 97 259 38 76 145 48 72 130 386), lower := (rows 97 259 38 76 145 48 72 128 256), losses := [] }

theorem u10809 : Upper (D 7) (R 7) [96,257,34,68,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10809 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10810 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 76 145 48 192 138 266), lower := (rows 97 259 38 76 145 48 192 128 256), losses := [] }

theorem u10810 : Upper (D 7) (R 7) [96,257,34,68,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10811 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,7)], upper := (rows 97 259 38 76 145 160 66 152 280), lower := (rows 97 259 38 76 145 160 66 128 256), losses := [] }

theorem u10811 : Upper (D 7) (R 7) [96,257,34,68,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10812 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 259 38 76 145 160 72 146 274), lower := (rows 97 259 38 76 145 160 72 128 256), losses := [] }

theorem u10812 : Upper (D 7) (R 7) [96,257,34,68,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10812 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10813 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 76 145 160 80 138 266), lower := (rows 97 259 38 76 145 160 80 128 256), losses := [] }

theorem u10813 : Upper (D 7) (R 7) [96,257,34,68,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10813 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10814 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 38 76 146 160 65 152 280), lower := (rows 97 259 38 76 146 160 65 128 256), losses := [] }

theorem u10814 : Upper (D 7) (R 7) [96,257,34,68,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10815 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 259 38 76 146 160 72 145 273), lower := (rows 97 259 38 76 146 160 72 128 256), losses := [] }

theorem u10815 : Upper (D 7) (R 7) [96,257,34,68,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10815 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10816 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 76 146 160 80 137 265), lower := (rows 97 259 38 76 146 160 80 128 256), losses := [] }

theorem u10816 : Upper (D 7) (R 7) [96,257,34,68,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10816 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10817 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 38 76 152 160 65 146 274), lower := (rows 97 259 38 76 152 160 65 128 256), losses := [] }

theorem u10817 : Upper (D 7) (R 7) [96,257,34,68,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10818 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,7)], upper := (rows 97 259 38 76 152 160 66 145 273), lower := (rows 97 259 38 76 152 160 66 128 256), losses := [] }

theorem u10818 : Upper (D 7) (R 7) [96,257,34,68,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10819 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 38 76 152 160 80 131 259), lower := (rows 97 259 38 76 152 160 80 128 256), losses := [] }

theorem u10819 : Upper (D 7) (R 7) [96,257,34,68,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10819 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10820 : Route 9 := (fun mask => (mask,id))

def c10820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10820 : Upper (D 7) (R 7) [96,257,34,80,129,128,2] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,129,128,2] 13 (by decide) (choices 1) [4,8] r10820 c10820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u805
  · exact u806

def b10821 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 88 145 160 68 138 266), lower := (rows 97 259 38 88 145 160 68 128 256), losses := [] }

theorem u10821 : Upper (D 7) (R 7) [96,257,34,80,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10821 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10822 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 145 160 72 134 262), lower := (rows 97 259 38 88 145 160 72 128 256), losses := [] }

theorem u10822 : Upper (D 7) (R 7) [96,257,34,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10822 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10823 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,1),(0,7),(2,0),(2,6)], upper := (rows 97 259 38 88 146 160 65 140 268), lower := (rows 97 259 38 88 146 160 65 128 256), losses := [] }

theorem u10823 : Upper (D 7) (R 7) [96,257,34,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10824 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 88 146 160 68 137 265), lower := (rows 97 259 38 88 146 160 68 128 256), losses := [] }

theorem u10824 : Upper (D 7) (R 7) [96,257,34,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10824 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10825 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 146 160 72 133 261), lower := (rows 97 259 38 88 146 160 72 128 256), losses := [] }

theorem u10825 : Upper (D 7) (R 7) [96,257,34,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10825 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10826 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(0,7),(3,1),(3,5)], upper := (rows 97 259 38 88 148 160 65 138 266), lower := (rows 97 259 38 88 148 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 67 132 260), good := (rows 65 323 478 88 412 128 65 128 256) }] }

theorem u10826 : Upper (D 7) (R 7) [96,257,34,80,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10827 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 65, targets := 128 },{ cop := 3, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 259 38 88 148 160 66 137 265), lower := (rows 97 259 38 88 148 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 176 70 128 256), good := (rows 96 322 102 120 252 160 66 160 256) },{ target := 5, region := (rows 1 2 4 24 16 0 70 128 256), good := (rows 65 323 70 88 220 128 66 128 256) }] }

theorem u10827 : Upper (D 7) (R 7) [96,257,34,80,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10828 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 148 160 72 131 259), lower := (rows 97 259 38 88 148 160 72 128 256), losses := [] }

theorem u10828 : Upper (D 7) (R 7) [96,257,34,80,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10828 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10829 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 38 137 146 40 68 208 336), lower := (rows 97 259 38 137 146 40 68 128 256), losses := [] }

theorem u10829 : Upper (D 7) (R 7) [96,257,34,129,130,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10829 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10830 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 259 38 137 146 40 80 196 324), lower := (rows 97 259 38 137 146 40 80 128 256), losses := [] }

theorem u10830 : Upper (D 7) (R 7) [96,257,34,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10830 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10831 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(4,0),(4,5)], upper := (rows 97 259 38 137 148 40 66 208 336), lower := (rows 97 259 38 137 148 40 66 128 256), losses := [] }

theorem u10831 : Upper (D 7) (R 7) [96,257,34,129,132,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10831 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10832 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 38 137 148 40 80 194 322), lower := (rows 97 259 38 137 148 40 80 128 256), losses := [] }

theorem u10832 : Upper (D 7) (R 7) [96,257,34,129,132,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10832 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10833 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 88 145 34 66 132 388), lower := (rows 97 259 44 88 145 34 66 128 256), losses := [] }

theorem u10833 : Upper (D 7) (R 7) [96,257,40,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10834 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 88 145 34 68 130 386), lower := (rows 97 259 44 88 145 34 68 128 256), losses := [] }

theorem u10834 : Upper (D 7) (R 7) [96,257,40,80,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10834 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10835 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 44 88 145 34 192 134 262), lower := (rows 97 259 44 88 145 34 192 128 256), losses := [] }

theorem u10835 : Upper (D 7) (R 7) [96,257,40,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10836 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,5),(1,6)], upper := (rows 97 259 44 88 148 34 65 130 386), lower := (rows 97 259 44 88 148 34 65 128 256), losses := [] }

theorem u10836 : Upper (D 7) (R 7) [96,257,40,80,132,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10837 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 88 148 34 66 129 385), lower := (rows 97 259 44 88 148 34 66 128 256), losses := [] }

theorem u10837 : Upper (D 7) (R 7) [96,257,40,80,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10838 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 44 88 148 34 192 131 259), lower := (rows 97 259 44 88 148 34 192 128 256), losses := [] }

theorem u10838 : Upper (D 7) (R 7) [96,257,40,80,132,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10839 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 137 146 34 68 208 336), lower := (rows 97 259 44 137 146 34 68 128 256), losses := [] }

theorem u10839 : Upper (D 7) (R 7) [96,257,40,129,130,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10839 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10840 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 259 44 137 146 34 80 196 324), lower := (rows 97 259 44 137 146 34 80 128 256), losses := [] }

theorem u10840 : Upper (D 7) (R 7) [96,257,40,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10840 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10841 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 259 44 137 146 48 66 196 324), lower := (rows 97 259 44 137 146 48 66 128 256), losses := [] }

theorem u10841 : Upper (D 7) (R 7) [96,257,40,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10841 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10842 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 44 137 146 48 68 194 322), lower := (rows 97 259 44 137 146 48 68 128 256), losses := [] }

theorem u10842 : Upper (D 7) (R 7) [96,257,40,129,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10842 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10843 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 137 148 34 66 208 336), lower := (rows 97 259 44 137 148 34 66 128 256), losses := [] }

theorem u10843 : Upper (D 7) (R 7) [96,257,40,129,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10844 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(3,5)], upper := (rows 97 259 44 137 148 34 80 194 322), lower := (rows 97 259 44 137 148 34 80 128 256), losses := [] }

theorem u10844 : Upper (D 7) (R 7) [96,257,40,129,132,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10844 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10845 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 137 208 34 66 148 276), lower := (rows 97 259 44 137 208 34 66 128 256), losses := [] }

theorem u10845 : Upper (D 7) (R 7) [96,257,40,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10846 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 137 208 34 68 146 274), lower := (rows 97 259 44 137 208 34 68 128 256), losses := [] }

theorem u10846 : Upper (D 7) (R 7) [96,257,40,129,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10846 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10847 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 44 137 208 34 80 134 262), lower := (rows 97 259 44 137 208 34 80 128 256), losses := [] }

theorem u10847 : Upper (D 7) (R 7) [96,257,40,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10847 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10848 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 97 259 44 138 145 48 66 196 324), lower := (rows 97 259 44 138 145 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 5 74 16 48 74 135 263), good := (rows 492 462 492 458 436 48 458 128 256) }] }

theorem u10848 : Upper (D 7) (R 7) [96,257,40,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10848 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10849 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 44 138 145 48 68 194 322), lower := (rows 97 259 44 138 145 48 68 128 256), losses := [] }

theorem u10849 : Upper (D 7) (R 7) [96,257,40,130,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10849 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10850 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 200 145 34 66 148 276), lower := (rows 97 259 44 200 145 34 66 128 256), losses := [] }

theorem u10850 : Upper (D 7) (R 7) [96,257,40,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10851 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 200 145 34 68 146 274), lower := (rows 97 259 44 200 145 34 68 128 256), losses := [] }

theorem u10851 : Upper (D 7) (R 7) [96,257,40,192,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10851 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10852 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 44 200 145 34 80 134 262), lower := (rows 97 259 44 200 145 34 80 128 256), losses := [] }

theorem u10852 : Upper (D 7) (R 7) [96,257,40,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10852 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10853 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 259 44 200 146 34 65 148 276), lower := (rows 97 259 44 200 146 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 73 50 50 64 183 311), good := (rows 508 446 444 200 438 438 460 128 256) }] }

theorem u10853 : Upper (D 7) (R 7) [96,257,40,192,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10854 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 200 146 34 68 145 273), lower := (rows 97 259 44 200 146 34 68 128 256), losses := [] }

theorem u10854 : Upper (D 7) (R 7) [96,257,40,192,130,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10854 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10855 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 44 200 146 34 80 133 261), lower := (rows 97 259 44 200 146 34 80 128 256), losses := [] }

theorem u10855 : Upper (D 7) (R 7) [96,257,40,192,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10855 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10856 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 259 44 200 146 48 65 134 262), lower := (rows 97 259 44 200 146 48 65 128 256), losses := [] }

theorem u10856 : Upper (D 7) (R 7) [96,257,40,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10856 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10857 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 259 44 200 146 48 66 133 261), lower := (rows 97 259 44 200 146 48 66 128 256), losses := [] }

theorem u10857 : Upper (D 7) (R 7) [96,257,40,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10857 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10858 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 259 44 200 146 48 68 131 259), lower := (rows 97 259 44 200 146 48 68 128 256), losses := [] }

theorem u10858 : Upper (D 7) (R 7) [96,257,40,192,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10858 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10859 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 259 44 200 148 34 65 146 274), lower := (rows 97 259 44 200 148 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 9 55 34 64 162 290), good := (rows 508 446 444 200 148 438 92 128 256) }] }

theorem u10859 : Upper (D 7) (R 7) [96,257,40,192,132,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10859
end Delivery.IrregularNine14.P07
