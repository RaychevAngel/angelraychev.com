import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0010

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 51 194 76 392 17 54 118 182 310), lower := (rows 51 194 76 392 17 32 64 128 256), losses := [] }

theorem u2820 : Upper (D 1) (R 1) [50,192,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 76 392 18 53 117 181 309), lower := (rows 51 194 76 392 18 32 64 128 256), losses := [] }

theorem u2821 : Upper (D 1) (R 1) [50,192,72,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 51, camps := [], pairs := [], upper := (rows 51 194 76 392 20 51 115 179 307), lower := (rows 51 194 76 392 20 32 64 128 256), losses := [] }

theorem u2822 : Upper (D 1) (R 1) [50,192,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 392 48 55 87 151 279), lower := (rows 51 194 76 392 48 32 64 128 256), losses := [] }

theorem u2823 : Upper (D 1) (R 1) [50,192,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 270, camps := [], pairs := [], upper := (rows 51 194 84 168 17 302 334 398 270), lower := (rows 51 194 84 168 17 32 64 128 256), losses := [] }

theorem u2824 : Upper (D 1) (R 1) [50,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 84 168 18 301 333 397 269), lower := (rows 51 194 84 168 18 32 64 128 256), losses := [] }

theorem u2825 : Upper (D 1) (R 1) [50,192,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 267, camps := [], pairs := [], upper := (rows 51 194 84 168 20 299 331 395 267), lower := (rows 51 194 84 168 20 32 64 128 256), losses := [] }

theorem u2826 : Upper (D 1) (R 1) [50,192,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 263, camps := [], pairs := [], upper := (rows 51 194 84 168 24 295 327 391 263), lower := (rows 51 194 84 168 24 32 64 128 256), losses := [] }

theorem u2827 : Upper (D 1) (R 1) [50,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2828 : PairBound 9 := { available := 15, camps := [], pairs := [], upper := (rows 51 194 84 168 272 47 79 143 271), lower := (rows 51 194 84 168 272 32 64 128 256), losses := [] }

theorem u2828 : Upper (D 1) (R 1) [50,192,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 84 265 18 172 236 172 428), lower := (rows 51 194 84 265 18 32 64 128 256), losses := [] }

theorem u2829 : Upper (D 1) (R 1) [50,192,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2830 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 194 84 265 20 170 234 170 426), lower := (rows 51 194 84 265 20 32 64 128 256), losses := [] }

theorem u2830 : Upper (D 1) (R 1) [50,192,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2830
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2831 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 194 84 265 24 166 230 166 422), lower := (rows 51 194 84 265 24 32 64 128 256), losses := [] }

theorem u2831 : Upper (D 1) (R 1) [50,192,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2832 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 265 48 174 206 142 398), lower := (rows 51 194 84 265 48 32 64 128 256), losses := [] }

theorem u2832 : Upper (D 1) (R 1) [50,192,80,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2833 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 265 144 46 110 174 302), lower := (rows 51 194 84 265 144 32 64 128 256), losses := [] }

theorem u2833 : Upper (D 1) (R 1) [50,192,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 172, camps := [], pairs := [], upper := (rows 51 194 84 266 17 172 236 172 428), lower := (rows 51 194 84 266 17 32 64 128 256), losses := [] }

theorem u2834 : Upper (D 1) (R 1) [50,192,80,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 194 84 266 20 169 233 169 425), lower := (rows 51 194 84 266 20 32 64 128 256), losses := [] }

theorem u2835 : Upper (D 1) (R 1) [50,192,80,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 194 84 266 24 165 229 165 421), lower := (rows 51 194 84 266 24 32 64 128 256), losses := [] }

theorem u2836 : Upper (D 1) (R 1) [50,192,80,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2837 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 266 48 173 205 141 397), lower := (rows 51 194 84 266 48 32 64 128 256), losses := [] }

theorem u2837 : Upper (D 1) (R 1) [50,192,80,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2837
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 266 144 45 109 173 301), lower := (rows 51 194 84 266 144 32 64 128 256), losses := [] }

theorem u2838 : Upper (D 1) (R 1) [50,192,80,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 194 84 268 17 170 234 170 426), lower := (rows 51 194 84 268 17 32 64 128 256), losses := [] }

theorem u2839 : Upper (D 1) (R 1) [50,192,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2839
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2840 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 84 268 18 169 233 169 425), lower := (rows 51 194 84 268 18 32 64 128 256), losses := [] }

theorem u2840 : Upper (D 1) (R 1) [50,192,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 194 84 268 24 163 227 163 419), lower := (rows 51 194 84 268 24 32 64 128 256), losses := [] }

theorem u2841 : Upper (D 1) (R 1) [50,192,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 268 48 171 203 139 395), lower := (rows 51 194 84 268 48 32 64 128 256), losses := [] }

theorem u2842 : Upper (D 1) (R 1) [50,192,80,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 268 144 43 107 171 299), lower := (rows 51 194 84 268 144 32 64 128 256), losses := [] }

theorem u2843 : Upper (D 1) (R 1) [50,192,80,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 51 194 84 296 17 174 206 142 398), lower := (rows 51 194 84 296 17 32 64 128 256), losses := [] }

theorem u2844 : Upper (D 1) (R 1) [50,192,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 84 296 18 173 205 141 397), lower := (rows 51 194 84 296 18 32 64 128 256), losses := [] }

theorem u2845 : Upper (D 1) (R 1) [50,192,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 51 194 84 296 20 171 203 139 395), lower := (rows 51 194 84 296 20 32 64 128 256), losses := [] }

theorem u2846 : Upper (D 1) (R 1) [50,192,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 51 194 84 296 24 167 199 135 391), lower := (rows 51 194 84 296 24 32 64 128 256), losses := [] }

theorem u2847 : Upper (D 1) (R 1) [50,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 296 144 47 79 143 271), lower := (rows 51 194 84 296 144 32 64 128 256), losses := [] }

theorem u2848 : Upper (D 1) (R 1) [50,192,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 46, camps := [], pairs := [], upper := (rows 51 194 84 392 17 46 110 174 302), lower := (rows 51 194 84 392 17 32 64 128 256), losses := [] }

theorem u2849 : Upper (D 1) (R 1) [50,192,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 84 392 18 45 109 173 301), lower := (rows 51 194 84 392 18 32 64 128 256), losses := [] }

theorem u2850 : Upper (D 1) (R 1) [50,192,80,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 51 194 84 392 20 43 107 171 299), lower := (rows 51 194 84 392 20 32 64 128 256), losses := [] }

theorem u2851 : Upper (D 1) (R 1) [50,192,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2851
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 39, camps := [], pairs := [], upper := (rows 51 194 84 392 24 39 103 167 295), lower := (rows 51 194 84 392 24 32 64 128 256), losses := [] }

theorem u2852 : Upper (D 1) (R 1) [50,192,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 392 48 47 79 143 271), lower := (rows 51 194 84 392 48 32 64 128 256), losses := [] }

theorem u2853 : Upper (D 1) (R 1) [50,192,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2853
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 104 18 228 196 196 452), lower := (rows 51 259 28 104 18 32 64 128 256), losses := [] }

theorem u2854 : Upper (D 1) (R 1) [50,257,24,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 51 259 28 104 20 226 194 194 450), lower := (rows 51 259 28 104 20 32 64 128 256), losses := [] }

theorem u2855 : Upper (D 1) (R 1) [50,257,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 104 80 166 198 134 390), lower := (rows 51 259 28 104 80 32 64 128 256), losses := [] }

theorem u2856 : Upper (D 1) (R 1) [50,257,24,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2857 : Route 9 := (fun mask => (mask,id))

def c2857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2857 : Upper (D 1) (R 1) [50,257,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,257,24,96,128] 13 (by decide) (choices 1) [2,4,64,128] r2857 c2857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u615
  · exact u616
  · exact u617
  · exact u618

def b2858 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 200 18 228 228 228 484), lower := (rows 51 259 28 200 18 32 64 128 256), losses := [] }

theorem u2858 : Upper (D 1) (R 1) [50,257,24,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2858
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 259 28 200 20 226 226 226 482), lower := (rows 51 259 28 200 20 32 64 128 256), losses := [] }

theorem u2859 : Upper (D 1) (R 1) [50,257,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2859
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 28 200 48 230 198 198 454), lower := (rows 51 259 28 200 48 32 64 128 256), losses := [] }

theorem u2860 : Upper (D 1) (R 1) [50,257,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 200 80 166 230 166 422), lower := (rows 51 259 28 200 80 32 64 128 256), losses := [] }

theorem u2861 : Upper (D 1) (R 1) [50,257,24,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 140 18 240 240 240 496), lower := (rows 51 259 76 140 18 32 64 128 256), losses := [] }

theorem u2862 : Upper (D 1) (R 1) [50,257,72,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 76 140 48 242 210 210 466), lower := (rows 51 259 76 140 48 32 64 128 256), losses := [] }

theorem u2863 : Upper (D 1) (R 1) [50,257,72,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 76 140 80 178 242 178 434), lower := (rows 51 259 76 140 80 32 64 128 256), losses := [] }

theorem u2864 : Upper (D 1) (R 1) [50,257,72,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2864
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 152 18 228 228 228 484), lower := (rows 51 259 76 152 18 32 64 128 256), losses := [] }

theorem u2865 : Upper (D 1) (R 1) [50,257,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 259 76 152 20 226 226 226 482), lower := (rows 51 259 76 152 20 32 64 128 256), losses := [] }

theorem u2866 : Upper (D 1) (R 1) [50,257,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 76 152 48 230 198 198 454), lower := (rows 51 259 76 152 48 32 64 128 256), losses := [] }

theorem u2867 : Upper (D 1) (R 1) [50,257,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2868 : Route 9 := (fun mask => (mask,id))

def c2868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2868 : Upper (D 1) (R 1) [50,257,72,144,64] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144,64] 13 (by decide) (choices 1) [2,4,128] r2868 c2868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u619
  · exact u620
  · exact u621

def b2869 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 259 76 152 144 102 102 230 358), lower := (rows 51 259 76 152 144 32 64 128 256), losses := [] }

theorem u2869 : Upper (D 1) (R 1) [50,257,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 104 18 172 204 140 396), lower := (rows 51 259 84 104 18 32 64 128 256), losses := [] }

theorem u2870 : Upper (D 1) (R 1) [50,257,80,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2870
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 51 259 84 104 20 170 202 138 394), lower := (rows 51 259 84 104 20 32 64 128 256), losses := [] }

theorem u2871 : Upper (D 1) (R 1) [50,257,80,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 259 84 104 24 166 198 134 390), lower := (rows 51 259 84 104 24 32 64 128 256), losses := [] }

theorem u2872 : Upper (D 1) (R 1) [50,257,80,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2872
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2873_2 : Upper (D 1) (R 1) [50,257,80,96,128,2] 13 :=
  permutation_upper _ _ _ [50,257,80,96,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u622

theorem m2873_4 : Upper (D 1) (R 1) [50,257,80,96,128,4] 13 :=
  permutation_upper _ _ _ [50,257,80,96,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u624

theorem m2873_8 : Upper (D 1) (R 1) [50,257,80,96,128,8] 13 :=
  permutation_upper _ _ _ [50,257,80,96,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u623

def r2873 : Route 9 := (fun mask => (mask,id))

def c2873 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2873 : Upper (D 1) (R 1) [50,257,80,96,128] 13 := by
  apply FastRouting.sound _ _ [50,257,80,96,128] 13 (by decide) (choices 1) [2,4,8,128] r2873 c2873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2873_2
  · exact m2873_4
  · exact m2873_8
  · exact u625

def b2874 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 168 18 236 204 204 460), lower := (rows 51 259 84 168 18 32 64 128 256), losses := [] }

theorem u2874 : Upper (D 1) (R 1) [50,257,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 51 259 84 168 20 234 202 202 458), lower := (rows 51 259 84 168 20 32 64 128 256), losses := [] }

theorem u2875 : Upper (D 1) (R 1) [50,257,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 51 259 84 168 24 230 198 198 454), lower := (rows 51 259 84 168 24 32 64 128 256), losses := [] }

theorem u2876 : Upper (D 1) (R 1) [50,257,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 84 168 80 174 206 142 398), lower := (rows 51 259 84 168 80 32 64 128 256), losses := [] }

theorem u2877 : Upper (D 1) (R 1) [50,257,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2877
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2878_2 : Upper (D 1) (R 1) [50,257,80,160,128,2] 13 :=
  permutation_upper _ _ _ [50,257,80,160,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u626

theorem m2878_4 : Upper (D 1) (R 1) [50,257,80,160,128,4] 13 :=
  permutation_upper _ _ _ [50,257,80,160,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u628

theorem m2878_8 : Upper (D 1) (R 1) [50,257,80,160,128,8] 13 :=
  permutation_upper _ _ _ [50,257,80,160,4,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u627

def r2878 : Route 9 := (fun mask => (mask,id))

def c2878 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2878 : Upper (D 1) (R 1) [50,257,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160,128] 13 (by decide) (choices 1) [2,4,8,64] r2878 c2878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2878_2
  · exact m2878_4
  · exact m2878_8
  · exact u629

def b2879 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 200 18 172 236 172 428), lower := (rows 51 259 84 200 18 32 64 128 256), losses := [] }

theorem u2879 : Upper (D 1) (R 1) [50,257,80,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2879
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P01
