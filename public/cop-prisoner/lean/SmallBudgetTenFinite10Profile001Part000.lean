import SmallBudgetTenFinite10Common

namespace Delivery.SmallBudgetTenFinite10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node3_cert : CutBound 10 := { lost := (rows 192 0 0 192 0 0 0 0 0 0), upper := (rows 49 194 196 776 784 800 64 128 256 512), lower := (rows 49 194 196 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1023 2 4 1023 1023 1023 0 1023 1023 1023), good := (rows 953 955 957 953 953 953 953 953 953 953) },{ target := 7, region := (rows 1023 2 4 1023 1023 1023 1023 0 1023 1023), good := (rows 889 891 893 889 889 889 889 889 889 889) }] }

theorem profile1_node3 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,192] 6 768 profile1_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,192] 6 768 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 10 := { lost := (rows 64 256 128 64 0 0 0 0 0 0), upper := (rows 49 194 324 904 912 928 64 128 256 512), lower := (rows 49 194 324 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1023 2 4 1023 1023 1023 0 1023 1023 1023), good := (rows 953 955 957 953 953 953 953 953 953 953) },{ target := 7, region := (rows 1 2 1023 8 16 32 1023 0 1023 1023), good := (rows 885 838 836 844 852 868 836 836 836 836) },{ target := 8, region := (rows 1 1023 4 8 16 32 1023 1023 0 1023), good := (rows 755 706 710 714 722 738 706 706 706 706) }] }

theorem profile1_node4 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,320] 6 896 profile1_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,320] 6 896 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 10 := { lost := (rows 0 768 192 0 0 0 0 0 0 0), upper := (rows 49 194 772 968 976 992 64 128 256 512), lower := (rows 49 194 772 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 8 16 32 0 1023 1023 1023), good := (rows 949 902 900 908 916 932 900 900 900 900) },{ target := 7, region := (rows 1 2 1023 8 16 32 1023 0 1023 1023), good := (rows 885 838 836 844 852 868 836 836 836 836) },{ target := 8, region := (rows 1 1023 4 8 16 32 1023 1023 0 1023), good := (rows 755 706 710 714 722 738 706 706 706 706) },{ target := 9, region := (rows 1 1023 4 8 16 32 1023 1023 1023 0), good := (rows 499 450 454 458 466 482 450 450 450 450) }] }

theorem profile1_node5 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,768] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,768] 6 960 profile1_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192,768] 6 960 profile1_node5_cert).mp (by decide +kernel))

def profile1_node2_column : Nat → Fin 10 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 544 => 5 | _ => 0

def profile1_node2_route : Route 10 := (fun mask => match mask with | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem profile1_node2 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48,192] 6 (by decide) (choices 2) [192,320,768] profile1_node2_route profile1_node2_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node5

def profile1_node1_column : Nat → Fin 10 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 544 => 5 | _ => 0

def profile1_node1_route : Route 10 := (fun mask => match mask with | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 576 => (192,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 640 => (192,(fun i => match i.val with | 6 => 9 | 9 => 6 | _ => i)) | 768 => (192,(fun i => match i.val with | 6 => 8 | 7 => 9 | 8 => 6 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [48] 6 (by decide) (choices 2) [192] profile1_node1_route profile1_node1_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node7_cert : CutBound 10 := { lost := (rows 128 128 64 64 0 0 0 0 0 0), upper := (rows 81 98 900 904 912 928 64 128 256 512), lower := (rows 81 98 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 17 34 4 8 16 32 1023 0 1023 1023), good := (rows 849 866 836 840 849 866 832 832 832 832) }] }

theorem profile1_node7 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,96] 6 896 profile1_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,96] 6 896 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 10 := { lost := (rows 384 320 0 0 0 0 0 0 0 0), upper := (rows 81 162 964 968 976 992 64 128 256 512), lower := (rows 81 162 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 34 4 8 16 32 0 1023 1023 1023), good := (rows 913 930 900 904 912 930 896 896 896 896) },{ target := 7, region := (rows 17 2 4 8 16 32 1023 0 1023 1023), good := (rows 849 866 836 840 849 864 832 832 832 832) },{ target := 8, region := (rows 17 34 4 8 16 32 1023 1023 0 1023), good := (rows 721 738 708 712 721 738 704 704 704 704) }] }

theorem profile1_node8 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,160] 6 960 profile1_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,160] 6 960 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 10 := { lost := (rows 384 256 64 64 0 0 0 0 0 0), upper := (rows 81 194 932 936 944 928 64 128 256 512), lower := (rows 81 194 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 17 2 4 8 16 32 1023 0 1023 1023), good := (rows 849 834 836 840 849 864 832 832 832 832) },{ target := 8, region := (rows 17 1023 4 8 16 32 1023 1023 0 1023), good := (rows 723 706 710 714 723 738 706 706 706 706) }] }

theorem profile1_node9 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,192] 6 928 profile1_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,192] 6 928 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : CutBound 10 := { lost := (rows 896 576 0 0 0 0 0 0 0 0), upper := (rows 81 386 996 1000 1008 992 64 128 256 512), lower := (rows 81 386 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 1023 4 8 16 32 0 1023 1023 1023), good := (rows 915 898 902 906 914 930 898 898 898 898) },{ target := 7, region := (rows 17 2 4 8 16 32 1023 0 1023 1023), good := (rows 849 834 836 840 849 864 832 832 832 832) },{ target := 8, region := (rows 17 2 4 8 16 32 1023 1023 0 1023), good := (rows 721 706 708 712 721 736 704 704 704 704) },{ target := 9, region := (rows 17 1023 4 8 16 32 1023 1023 1023 0), good := (rows 467 450 454 458 467 482 450 450 450 450) }] }

theorem profile1_node10 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,384] 6 992 profile1_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80,384] 6 992 profile1_node10_cert).mp (by decide +kernel))

def profile1_node6_column : Nat → Fin 10 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | _ => 0

def profile1_node6_route : Route 10 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 544 => (160,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 576 => (192,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 640 => (384,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 768 => (384,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile1_node6 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [80] 6 (by decide) (choices 2) [96,160,192,384] profile1_node6_route profile1_node6_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node7
  · exact profile1_node8
  · exact profile1_node9
  · exact profile1_node10

def profile1_node13_cert : CutBound 10 := { lost := (rows 0 192 0 192 0 0 0 0 0 0), upper := (rows 193 50 196 776 784 800 64 128 256 512), lower := (rows 193 50 196 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 1023 4 1023 1023 1023 0 1023 1023 1023), good := (rows 955 954 958 954 954 954 954 954 954 954) },{ target := 7, region := (rows 1 1023 4 1023 1023 1023 1023 0 1023 1023), good := (rows 891 890 894 890 890 890 890 890 890 890) }] }

theorem profile1_node13 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,192] 6 768 profile1_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,192] 6 768 profile1_node13_cert).mp (by decide +kernel))

def profile1_node14_cert : CutBound 10 := { lost := (rows 256 64 128 64 0 0 0 0 0 0), upper := (rows 193 50 324 904 912 928 64 128 256 512), lower := (rows 193 50 324 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 1023 4 1023 1023 1023 0 1023 1023 1023), good := (rows 955 954 958 954 954 954 954 954 954 954) },{ target := 7, region := (rows 1 2 1023 8 16 32 1023 0 1023 1023), good := (rows 837 886 836 844 852 868 836 836 836 836) },{ target := 8, region := (rows 1023 2 4 8 16 32 1023 1023 0 1023), good := (rows 705 755 709 713 721 737 705 705 705 705) }] }

theorem profile1_node14 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,320] 6 896 profile1_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,320] 6 896 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : CutBound 10 := { lost := (rows 768 0 192 0 0 0 0 0 0 0), upper := (rows 193 50 772 968 976 992 64 128 256 512), lower := (rows 193 50 772 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 8 16 32 0 1023 1023 1023), good := (rows 901 950 900 908 916 932 900 900 900 900) },{ target := 7, region := (rows 1 2 1023 8 16 32 1023 0 1023 1023), good := (rows 837 886 836 844 852 868 836 836 836 836) },{ target := 8, region := (rows 1023 2 4 8 16 32 1023 1023 0 1023), good := (rows 705 755 709 713 721 737 705 705 705 705) },{ target := 9, region := (rows 1023 2 4 8 16 32 1023 1023 1023 0), good := (rows 449 499 453 457 465 481 449 449 449 449) }] }

theorem profile1_node15 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,768] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,768] 6 960 profile1_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48,768] 6 960 profile1_node15_cert).mp (by decide +kernel))

def profile1_node12_column : Nat → Fin 10 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 544 => 5 | _ => 0

def profile1_node12_route : Route 10 := (fun mask => match mask with | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem profile1_node12 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,48] 6 (by decide) (choices 2) [192,320,768] profile1_node12_route profile1_node12_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node13
  · exact profile1_node14
  · exact profile1_node15

def profile1_node16_cert : CutBound 10 := { lost := (rows 256 384 64 64 0 0 0 0 0 0), upper := (rows 193 82 932 936 944 928 64 128 256 512), lower := (rows 193 82 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 1 18 4 8 16 32 1023 0 1023 1023), good := (rows 833 850 836 840 850 864 832 832 832 832) },{ target := 8, region := (rows 1023 18 4 8 16 32 1023 1023 0 1023), good := (rows 705 723 709 713 723 737 705 705 705 705) }] }

theorem profile1_node16 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,80] 6 928 profile1_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,80] 6 928 profile1_node16_cert).mp (by decide +kernel))

def profile1_node17_cert : CutBound 10 := { lost := (rows 0 0 192 192 0 0 0 0 0 0), upper := (rows 193 194 820 824 816 816 64 128 256 512), lower := (rows 193 194 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 1 2 1023 1023 1023 1023 1023 0 1023 1023), good := (rows 893 894 892 892 892 892 892 892 892 892) }] }

theorem profile1_node17 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,192] 6 816 profile1_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,192] 6 816 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 10 := { lost := (rows 768 704 0 0 0 0 0 0 0 0), upper := (rows 193 274 996 1000 1008 992 64 128 256 512), lower := (rows 193 274 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 18 4 8 16 32 0 1023 1023 1023), good := (rows 897 914 900 904 914 928 896 896 896 896) },{ target := 7, region := (rows 1 18 4 8 16 32 1023 0 1023 1023), good := (rows 833 850 836 840 850 864 832 832 832 832) },{ target := 8, region := (rows 1023 2 4 8 16 32 1023 1023 0 1023), good := (rows 705 723 709 713 721 737 705 705 705 705) },{ target := 9, region := (rows 1023 18 4 8 16 32 1023 1023 1023 0), good := (rows 449 467 453 457 467 481 449 449 449 449) }] }

theorem profile1_node18 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,272] 6 992 profile1_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,272] 6 992 profile1_node18_cert).mp (by decide +kernel))

def profile1_node19_cert : CutBound 10 := { lost := (rows 256 128 64 64 0 0 0 0 0 0), upper := (rows 193 322 948 952 944 944 64 128 256 512), lower := (rows 193 322 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 1 1023 4 8 16 32 1023 0 1023 1023), good := (rows 835 834 838 842 850 866 834 834 834 834) },{ target := 8, region := (rows 1023 2 4 8 16 32 1023 1023 0 1023), good := (rows 705 707 709 713 721 737 705 705 705 705) }] }

theorem profile1_node19 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,320] 6 944 profile1_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,320] 6 944 profile1_node19_cert).mp (by decide +kernel))

def profile1_node20_cert : CutBound 10 := { lost := (rows 768 192 0 0 0 0 0 0 0 0), upper := (rows 193 770 1012 1016 1008 1008 64 128 256 512), lower := (rows 193 770 4 8 16 32 64 128 256 512), losses := [{ target := 6, region := (rows 1 1023 4 8 16 32 0 1023 1023 1023), good := (rows 899 898 902 906 914 930 898 898 898 898) },{ target := 7, region := (rows 1 1023 4 8 16 32 1023 0 1023 1023), good := (rows 835 834 838 842 850 866 834 834 834 834) },{ target := 8, region := (rows 1023 2 4 8 16 32 1023 1023 0 1023), good := (rows 705 707 709 713 721 737 705 705 705 705) },{ target := 9, region := (rows 1023 2 4 8 16 32 1023 1023 1023 0), good := (rows 449 451 453 457 465 481 449 449 449 449) }] }

theorem profile1_node20 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,768] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,768] 6 1008 profile1_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192,768] 6 1008 profile1_node20_cert).mp (by decide +kernel))

def profile1_node11_column : Nat → Fin 10 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | _ => 0

def profile1_node11_route : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem profile1_node11 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [192] 6 (by decide) (choices 2) [48,80,192,272,320,768] profile1_node11_route profile1_node11_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node12
  · exact profile1_node16
  · exact profile1_node17
  · exact profile1_node18
  · exact profile1_node19
  · exact profile1_node20

def profile1_node0_column : Nat → Fin 10 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | _ => 0

def profile1_node0_route : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 528 => (80,(fun i => match i.val with | 6 => 9 | 9 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 544 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 9 | 9 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 576 => (192,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 640 => (192,(fun i => match i.val with | 6 => 9 | 9 => 6 | _ => i)) | 768 => (192,(fun i => match i.val with | 6 => 8 | 7 => 9 | 8 => 6 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [] 6 (by decide) (choices 2) [48,80,192] profile1_node0_route profile1_node0_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node6
  · exact profile1_node11

theorem profile1 : Upper (D (n:=10) [32,32,32,32,17,17,2,2,2,2]) (R (n:=10) [32,32,32,32,17,17,2,2,2,2]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite10
