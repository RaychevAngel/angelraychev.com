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

def b11880 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 28 168 208 37 101 165 293), lower := (rows 67 259 28 168 208 32 64 128 256), losses := [] }

theorem u11880 : Upper (D 8) (R 8) [66,257,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11881 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 88 176 240 176 432), lower := (rows 67 259 37 44 88 32 64 128 256), losses := [] }

theorem u11881 : Upper (D 8) (R 8) [66,257,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11882 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 112 184 216 152 408), lower := (rows 67 259 37 44 112 32 64 128 256), losses := [] }

theorem u11882 : Upper (D 8) (R 8) [66,257,33,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11883 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 152 240 240 240 496), lower := (rows 67 259 37 44 152 32 64 128 256), losses := [] }

theorem u11883 : Upper (D 8) (R 8) [66,257,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11884 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 176 248 216 216 472), lower := (rows 67 259 37 44 176 32 64 128 256), losses := [] }

theorem u11884 : Upper (D 8) (R 8) [66,257,33,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11885 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 44 208 184 248 184 440), lower := (rows 67 259 37 44 208 32 64 128 256), losses := [] }

theorem u11885 : Upper (D 8) (R 8) [66,257,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11886 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 56 84 168 232 168 424), lower := (rows 67 259 37 56 84 32 64 128 256), losses := [] }

theorem u11886 : Upper (D 8) (R 8) [66,257,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11887 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 56 148 232 232 232 488), lower := (rows 67 259 37 56 148 32 64 128 256), losses := [] }

theorem u11887 : Upper (D 8) (R 8) [66,257,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11888 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 56 152 228 228 228 484), lower := (rows 67 259 37 56 152 32 64 128 256), losses := [] }

theorem u11888 : Upper (D 8) (R 8) [66,257,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11889 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 56 208 172 236 172 428), lower := (rows 67 259 37 56 208 32 64 128 256), losses := [] }

theorem u11889 : Upper (D 8) (R 8) [66,257,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11890 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 76 152 176 240 176 432), lower := (rows 67 259 37 76 152 32 64 128 256), losses := [] }

theorem u11890 : Upper (D 8) (R 8) [66,257,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11891 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 76 176 184 248 184 440), lower := (rows 67 259 37 76 176 32 64 128 256), losses := [] }

theorem u11891 : Upper (D 8) (R 8) [66,257,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11892 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 88 148 168 232 168 424), lower := (rows 67 259 37 88 148 32 64 128 256), losses := [] }

theorem u11892 : Upper (D 8) (R 8) [66,257,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11893 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 88 176 172 236 172 428), lower := (rows 67 259 37 88 176 32 64 128 256), losses := [] }

theorem u11893 : Upper (D 8) (R 8) [66,257,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11894 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 104 148 184 248 184 440), lower := (rows 67 259 37 104 148 32 64 128 256), losses := [] }

theorem u11894 : Upper (D 8) (R 8) [66,257,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11895 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 104 152 180 244 180 436), lower := (rows 67 259 37 104 152 32 64 128 256), losses := [] }

theorem u11895 : Upper (D 8) (R 8) [66,257,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11896 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 104 176 188 220 156 412), lower := (rows 67 259 37 104 176 32 64 128 256), losses := [] }

theorem u11896 : Upper (D 8) (R 8) [66,257,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11897 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 140 176 120 120 248 376), lower := (rows 67 259 37 140 176 32 64 128 256), losses := [] }

theorem u11897 : Upper (D 8) (R 8) [66,257,33,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11898 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 140 208 56 120 184 312), lower := (rows 67 259 37 140 208 32 64 128 256), losses := [] }

theorem u11898 : Upper (D 8) (R 8) [66,257,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11899 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 259 37 168 208 60 124 188 316), lower := (rows 67 259 37 168 208 32 64 128 256), losses := [] }

theorem u11899 : Upper (D 8) (R 8) [66,257,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11900 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 44 112 177 209 145 401), lower := (rows 67 259 44 44 112 32 64 128 256), losses := [] }

theorem u11900 : Upper (D 8) (R 8) [66,257,40,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11901 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 44 176 241 209 209 465), lower := (rows 67 259 44 44 176 32 64 128 256), losses := [] }

theorem u11901 : Upper (D 8) (R 8) [66,257,40,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11902 : PairBound 9 := { available := 177, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 44 208 177 241 177 433), lower := (rows 67 259 44 44 208 32 64 128 256), losses := [] }

theorem u11902 : Upper (D 8) (R 8) [66,257,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11903 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 84 161 225 161 417), lower := (rows 67 259 44 56 84 32 64 128 256), losses := [] }

theorem u11903 : Upper (D 8) (R 8) [66,257,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11904 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 112 165 197 133 389), lower := (rows 67 259 44 56 112 32 64 128 256), losses := [] }

theorem u11904 : Upper (D 8) (R 8) [66,257,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11905 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 148 225 225 225 481), lower := (rows 67 259 44 56 148 32 64 128 256), losses := [] }

theorem u11905 : Upper (D 8) (R 8) [66,257,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11906 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 176 229 197 197 453), lower := (rows 67 259 44 56 176 32 64 128 256), losses := [] }

theorem u11906 : Upper (D 8) (R 8) [66,257,40,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11907 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 56 208 165 229 165 421), lower := (rows 67 259 44 56 208 32 64 128 256), losses := [] }

theorem u11907 : Upper (D 8) (R 8) [66,257,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11908 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 73 148 176 240 176 432), lower := (rows 67 259 44 73 148 32 64 128 256), losses := [] }

theorem u11908 : Upper (D 8) (R 8) [66,257,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11909 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 73 176 180 244 180 436), lower := (rows 67 259 44 73 176 32 64 128 256), losses := [] }

theorem u11909 : Upper (D 8) (R 8) [66,257,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11910 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 76 176 177 241 177 433), lower := (rows 67 259 44 76 176 32 64 128 256), losses := [] }

theorem u11910 : Upper (D 8) (R 8) [66,257,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11911 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 88 145 164 228 164 420), lower := (rows 67 259 44 88 145 32 64 128 256), losses := [] }

theorem u11911 : Upper (D 8) (R 8) [66,257,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11912 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 88 148 161 225 161 417), lower := (rows 67 259 44 88 148 32 64 128 256), losses := [] }

theorem u11912 : Upper (D 8) (R 8) [66,257,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11913 : Route 9 := (fun mask => (mask,id))

def c11913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11913 : Upper (D 8) (R 8) [66,257,40,80,160] 13 := by
  apply FastRouting.sound _ _ [66,257,40,80,160] 13 (by decide) (choices 1) [1,4,128] r11913 c11913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3811
  · exact u3812
  · exact u3813

def b11914 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 104 148 177 241 177 433), lower := (rows 67 259 44 104 148 32 64 128 256), losses := [] }

theorem u11914 : Upper (D 8) (R 8) [66,257,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11915 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 104 176 181 213 149 405), lower := (rows 67 259 44 104 176 32 64 128 256), losses := [] }

theorem u11915 : Upper (D 8) (R 8) [66,257,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11916 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 84 176 240 176 432), lower := (rows 67 259 44 137 84 32 64 128 256), losses := [] }

theorem u11916 : Upper (D 8) (R 8) [66,257,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11917 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 112 180 244 180 436), lower := (rows 67 259 44 137 112 32 64 128 256), losses := [] }

theorem u11917 : Upper (D 8) (R 8) [66,257,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11918 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 148 112 112 240 368), lower := (rows 67 259 44 137 148 32 64 128 256), losses := [] }

theorem u11918 : Upper (D 8) (R 8) [66,257,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11919 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 176 116 116 244 372), lower := (rows 67 259 44 137 176 32 64 128 256), losses := [] }

theorem u11919 : Upper (D 8) (R 8) [66,257,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11920 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 137 208 52 116 180 308), lower := (rows 67 259 44 137 208 32 64 128 256), losses := [] }

theorem u11920 : Upper (D 8) (R 8) [66,257,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11921 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 140 81 176 240 176 432), lower := (rows 67 259 44 140 81 32 64 128 256), losses := [] }

theorem u11921 : Upper (D 8) (R 8) [66,257,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11922 : Route 9 := (fun mask => (mask,id))

def c11922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11922 : Upper (D 8) (R 8) [66,257,40,132,96] 13 := by
  apply FastRouting.sound _ _ [66,257,40,132,96] 13 (by decide) (choices 1) [1,16,128] r11922 c11922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3814
  · exact u3815
  · exact u3816

def b11923 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 140 145 112 112 240 368), lower := (rows 67 259 44 140 145 32 64 128 256), losses := [] }

theorem u11923 : Upper (D 8) (R 8) [66,257,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11924 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 140 176 113 113 241 369), lower := (rows 67 259 44 140 176 32 64 128 256), losses := [] }

theorem u11924 : Upper (D 8) (R 8) [66,257,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11925 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 140 208 49 113 177 305), lower := (rows 67 259 44 140 208 32 64 128 256), losses := [] }

theorem u11925 : Upper (D 8) (R 8) [66,257,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11926 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 152 81 164 228 164 420), lower := (rows 67 259 44 152 81 32 64 128 256), losses := [] }

theorem u11926 : Upper (D 8) (R 8) [66,257,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11927 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 259 44 152 84 161 225 161 417), lower := (rows 67 259 44 152 84 32 64 128 256), losses := [] }

theorem u11927 : Upper (D 8) (R 8) [66,257,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11928 : Route 9 := (fun mask => (mask,id))

def c11928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11928 : Upper (D 8) (R 8) [66,257,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,257,40,144,96] 13 (by decide) (choices 1) [1,4,128] r11928 c11928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3817
  · exact u3818
  · exact u3819

def b11929 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 152 145 100 100 228 356), lower := (rows 67 259 44 152 145 32 64 128 256), losses := [] }

theorem u11929 : Upper (D 8) (R 8) [66,257,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11930 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 152 148 97 97 225 353), lower := (rows 67 259 44 152 148 32 64 128 256), losses := [] }

theorem u11930 : Upper (D 8) (R 8) [66,257,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11931 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 152 176 101 101 229 357), lower := (rows 67 259 44 152 176 32 64 128 256), losses := [] }

theorem u11931 : Upper (D 8) (R 8) [66,257,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11932 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 152 208 37 101 165 293), lower := (rows 67 259 44 152 208 32 64 128 256), losses := [] }

theorem u11932 : Upper (D 8) (R 8) [66,257,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11933 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 84 177 241 177 433), lower := (rows 67 259 44 168 84 32 64 128 256), losses := [] }

theorem u11933 : Upper (D 8) (R 8) [66,257,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11934 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 112 181 213 149 405), lower := (rows 67 259 44 168 112 32 64 128 256), losses := [] }

theorem u11934 : Upper (D 8) (R 8) [66,257,40,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11935 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 148 113 113 241 369), lower := (rows 67 259 44 168 148 32 64 128 256), losses := [] }

theorem u11935 : Upper (D 8) (R 8) [66,257,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11936 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 176 117 85 213 341), lower := (rows 67 259 44 168 176 32 64 128 256), losses := [] }

theorem u11936 : Upper (D 8) (R 8) [66,257,40,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11937 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 168 208 53 117 181 309), lower := (rows 67 259 44 168 208 32 64 128 256), losses := [] }

theorem u11937 : Upper (D 8) (R 8) [66,257,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11938 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 200 145 52 116 180 308), lower := (rows 67 259 44 200 145 32 64 128 256), losses := [] }

theorem u11938 : Upper (D 8) (R 8) [66,257,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11939 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 200 148 49 113 177 305), lower := (rows 67 259 44 200 148 32 64 128 256), losses := [] }

theorem u11939 : Upper (D 8) (R 8) [66,257,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11939
end Delivery.IrregularNine14.P08
