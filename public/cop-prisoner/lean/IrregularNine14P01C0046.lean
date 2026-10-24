import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 387, camps := [], pairs := [], upper := (rows 51 194 28 104 20 419 451 387 387), lower := (rows 51 194 28 104 20 32 64 128 256), losses := [] }

theorem u2760 : Upper (D 1) (R 1) [50,192,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 104 144 295 327 391 263), lower := (rows 51 194 28 104 144 32 64 128 256), losses := [] }

theorem u2761 : Upper (D 1) (R 1) [50,192,24,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 51 194 28 104 272 167 199 135 391), lower := (rows 51 194 28 104 272 32 64 128 256), losses := [] }

theorem u2762 : Upper (D 1) (R 1) [50,192,24,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 51 194 28 266 17 228 228 228 484), lower := (rows 51 194 28 266 17 32 64 128 256), losses := [] }

theorem u2763 : Upper (D 1) (R 1) [50,192,24,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 194 28 266 20 225 225 225 481), lower := (rows 51 194 28 266 20 32 64 128 256), losses := [] }

theorem u2764 : Upper (D 1) (R 1) [50,192,24,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2765 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 28 266 48 229 197 197 453), lower := (rows 51 194 28 266 48 32 64 128 256), losses := [] }

theorem u2765 : Upper (D 1) (R 1) [50,192,24,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2765
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2766 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 266 80 165 229 165 421), lower := (rows 51 194 28 266 80 32 64 128 256), losses := [] }

theorem u2766 : Upper (D 1) (R 1) [50,192,24,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 51 194 28 296 17 230 198 198 454), lower := (rows 51 194 28 296 17 32 64 128 256), losses := [] }

theorem u2767 : Upper (D 1) (R 1) [50,192,24,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 28 296 18 229 197 197 453), lower := (rows 51 194 28 296 18 32 64 128 256), losses := [] }

theorem u2768 : Upper (D 1) (R 1) [50,192,24,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 51 194 28 296 20 227 195 195 451), lower := (rows 51 194 28 296 20 32 64 128 256), losses := [] }

theorem u2769 : Upper (D 1) (R 1) [50,192,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 296 80 167 199 135 391), lower := (rows 51 194 28 296 80 32 64 128 256), losses := [] }

theorem u2770 : Upper (D 1) (R 1) [50,192,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 194 28 328 17 166 230 166 422), lower := (rows 51 194 28 328 17 32 64 128 256), losses := [] }

theorem u2771 : Upper (D 1) (R 1) [50,192,24,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 28 328 18 165 229 165 421), lower := (rows 51 194 28 328 18 32 64 128 256), losses := [] }

theorem u2772 : Upper (D 1) (R 1) [50,192,24,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 194 28 328 20 163 227 163 419), lower := (rows 51 194 28 328 20 32 64 128 256), losses := [] }

theorem u2773 : Upper (D 1) (R 1) [50,192,24,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 28 328 48 167 199 135 391), lower := (rows 51 194 28 328 48 32 64 128 256), losses := [] }

theorem u2774 : Upper (D 1) (R 1) [50,192,24,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 39, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 328 144 39 103 167 295), lower := (rows 51 194 28 328 144 32 64 128 256), losses := [] }

theorem u2775 : Upper (D 1) (R 1) [50,192,24,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 69 140 18 312 376 440 312), lower := (rows 51 194 69 140 18 32 64 128 256), losses := [] }

theorem u2776 : Upper (D 1) (R 1) [50,192,65,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 306, camps := [], pairs := [], upper := (rows 51 194 69 140 24 306 370 434 306), lower := (rows 51 194 69 140 24 32 64 128 256), losses := [] }

theorem u2777 : Upper (D 1) (R 1) [50,192,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 140 48 314 346 410 282), lower := (rows 51 194 69 140 48 32 64 128 256), losses := [] }

theorem u2778 : Upper (D 1) (R 1) [50,192,65,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 194 69 140 272 58 122 186 314), lower := (rows 51 194 69 140 272 32 64 128 256), losses := [] }

theorem u2779 : Upper (D 1) (R 1) [50,192,65,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2779
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 69 152 18 300 364 428 300), lower := (rows 51 194 69 152 18 32 64 128 256), losses := [] }

theorem u2780 : Upper (D 1) (R 1) [50,192,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 298, camps := [], pairs := [], upper := (rows 51 194 69 152 20 298 362 426 298), lower := (rows 51 194 69 152 20 32 64 128 256), losses := [] }

theorem u2781 : Upper (D 1) (R 1) [50,192,65,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 294, camps := [], pairs := [], upper := (rows 51 194 69 152 24 294 358 422 294), lower := (rows 51 194 69 152 24 32 64 128 256), losses := [] }

theorem u2782 : Upper (D 1) (R 1) [50,192,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 152 48 302 334 398 270), lower := (rows 51 194 69 152 48 32 64 128 256), losses := [] }

theorem u2783 : Upper (D 1) (R 1) [50,192,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 46, camps := [], pairs := [], upper := (rows 51 194 69 152 272 46 110 174 302), lower := (rows 51 194 69 152 272 32 64 128 256), losses := [] }

theorem u2784 : Upper (D 1) (R 1) [50,192,65,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 184, camps := [], pairs := [], upper := (rows 51 194 69 266 20 184 248 184 440), lower := (rows 51 194 69 266 20 32 64 128 256), losses := [] }

theorem u2785 : Upper (D 1) (R 1) [50,192,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2785
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 180, camps := [], pairs := [], upper := (rows 51 194 69 266 24 180 244 180 436), lower := (rows 51 194 69 266 24 32 64 128 256), losses := [] }

theorem u2786 : Upper (D 1) (R 1) [50,192,65,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 266 48 188 220 156 412), lower := (rows 51 194 69 266 48 32 64 128 256), losses := [] }

theorem u2787 : Upper (D 1) (R 1) [50,192,65,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 266 144 60 124 188 316), lower := (rows 51 194 69 266 144 32 64 128 256), losses := [] }

theorem u2788 : Upper (D 1) (R 1) [50,192,65,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 69 268 18 184 248 184 440), lower := (rows 51 194 69 268 18 32 64 128 256), losses := [] }

theorem u2789 : Upper (D 1) (R 1) [50,192,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 194 69 268 24 178 242 178 434), lower := (rows 51 194 69 268 24 32 64 128 256), losses := [] }

theorem u2790 : Upper (D 1) (R 1) [50,192,65,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 268 48 186 218 154 410), lower := (rows 51 194 69 268 48 32 64 128 256), losses := [] }

theorem u2791 : Upper (D 1) (R 1) [50,192,65,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 268 144 58 122 186 314), lower := (rows 51 194 69 268 144 32 64 128 256), losses := [] }

theorem u2792 : Upper (D 1) (R 1) [50,192,65,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2793 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 69 280 18 172 236 172 428), lower := (rows 51 194 69 280 18 32 64 128 256), losses := [] }

theorem u2793 : Upper (D 1) (R 1) [50,192,65,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 194 69 280 20 170 234 170 426), lower := (rows 51 194 69 280 20 32 64 128 256), losses := [] }

theorem u2794 : Upper (D 1) (R 1) [50,192,65,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 194 69 280 24 166 230 166 422), lower := (rows 51 194 69 280 24 32 64 128 256), losses := [] }

theorem u2795 : Upper (D 1) (R 1) [50,192,65,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 280 48 174 206 142 398), lower := (rows 51 194 69 280 48 32 64 128 256), losses := [] }

theorem u2796 : Upper (D 1) (R 1) [50,192,65,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2796
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 280 144 46 110 174 302), lower := (rows 51 194 69 280 144 32 64 128 256), losses := [] }

theorem u2797 : Upper (D 1) (R 1) [50,192,65,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2797
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 69 392 18 60 124 188 316), lower := (rows 51 194 69 392 18 32 64 128 256), losses := [] }

theorem u2798 : Upper (D 1) (R 1) [50,192,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2799 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 194 69 392 20 58 122 186 314), lower := (rows 51 194 69 392 20 32 64 128 256), losses := [] }

theorem u2799 : Upper (D 1) (R 1) [50,192,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2800 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 51 194 69 392 24 54 118 182 310), lower := (rows 51 194 69 392 24 32 64 128 256), losses := [] }

theorem u2800 : Upper (D 1) (R 1) [50,192,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 69 392 48 62 94 158 286), lower := (rows 51 194 69 392 48 32 64 128 256), losses := [] }

theorem u2801 : Upper (D 1) (R 1) [50,192,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 294, camps := [], pairs := [], upper := (rows 51 194 76 152 17 294 358 422 294), lower := (rows 51 194 76 152 17 32 64 128 256), losses := [] }

theorem u2802 : Upper (D 1) (R 1) [50,192,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2803 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 76 152 18 293 357 421 293), lower := (rows 51 194 76 152 18 32 64 128 256), losses := [] }

theorem u2803 : Upper (D 1) (R 1) [50,192,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2804 : PairBound 9 := { available := 291, camps := [], pairs := [], upper := (rows 51 194 76 152 20 291 355 419 291), lower := (rows 51 194 76 152 20 32 64 128 256), losses := [] }

theorem u2804 : Upper (D 1) (R 1) [50,192,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 152 48 295 327 391 263), lower := (rows 51 194 76 152 48 32 64 128 256), losses := [] }

theorem u2805 : Upper (D 1) (R 1) [50,192,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 39, camps := [], pairs := [], upper := (rows 51 194 76 152 272 39 103 167 295), lower := (rows 51 194 76 152 272 32 64 128 256), losses := [] }

theorem u2806 : Upper (D 1) (R 1) [50,192,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 76 265 18 180 244 180 436), lower := (rows 51 194 76 265 18 32 64 128 256), losses := [] }

theorem u2807 : Upper (D 1) (R 1) [50,192,72,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 194 76 265 20 178 242 178 434), lower := (rows 51 194 76 265 20 32 64 128 256), losses := [] }

theorem u2808 : Upper (D 1) (R 1) [50,192,72,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 265 48 182 214 150 406), lower := (rows 51 194 76 265 48 32 64 128 256), losses := [] }

theorem u2809 : Upper (D 1) (R 1) [50,192,72,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 265 144 54 118 182 310), lower := (rows 51 194 76 265 144 32 64 128 256), losses := [] }

theorem u2810 : Upper (D 1) (R 1) [50,192,72,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 180, camps := [], pairs := [], upper := (rows 51 194 76 266 17 180 244 180 436), lower := (rows 51 194 76 266 17 32 64 128 256), losses := [] }

theorem u2811 : Upper (D 1) (R 1) [50,192,72,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 194 76 266 20 177 241 177 433), lower := (rows 51 194 76 266 20 32 64 128 256), losses := [] }

theorem u2812 : Upper (D 1) (R 1) [50,192,72,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 266 48 181 213 149 405), lower := (rows 51 194 76 266 48 32 64 128 256), losses := [] }

theorem u2813 : Upper (D 1) (R 1) [50,192,72,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2814 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 266 144 53 117 181 309), lower := (rows 51 194 76 266 144 32 64 128 256), losses := [] }

theorem u2814 : Upper (D 1) (R 1) [50,192,72,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2815 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 194 76 280 17 166 230 166 422), lower := (rows 51 194 76 280 17 32 64 128 256), losses := [] }

theorem u2815 : Upper (D 1) (R 1) [50,192,72,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2816 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 76 280 18 165 229 165 421), lower := (rows 51 194 76 280 18 32 64 128 256), losses := [] }

theorem u2816 : Upper (D 1) (R 1) [50,192,72,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 194 76 280 20 163 227 163 419), lower := (rows 51 194 76 280 20 32 64 128 256), losses := [] }

theorem u2817 : Upper (D 1) (R 1) [50,192,72,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 280 48 167 199 135 391), lower := (rows 51 194 76 280 48 32 64 128 256), losses := [] }

theorem u2818 : Upper (D 1) (R 1) [50,192,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 39, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 280 144 39 103 167 295), lower := (rows 51 194 76 280 144 32 64 128 256), losses := [] }

theorem u2819 : Upper (D 1) (R 1) [50,192,72,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2819
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P01
