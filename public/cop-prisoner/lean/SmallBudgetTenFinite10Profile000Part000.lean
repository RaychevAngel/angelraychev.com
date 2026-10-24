import SmallBudgetTenFinite10Common

namespace Delivery.SmallBudgetTenFinite10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 10 := { lost := (rows 384 384 96 96 96 0 0 0 0 0), upper := (rows 97 98 900 904 912 32 64 128 256 512), lower := (rows 97 98 4 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 1023 1023 1023 0 1023 1023 1023 1023), good := (rows 989 990 988 988 988 988 988 988 988 988) },{ target := 6, region := (rows 1 2 1023 1023 1023 1023 0 1023 1023 1023), good := (rows 957 958 956 956 956 956 956 956 956 956) },{ target := 7, region := (rows 1023 1023 4 8 16 1023 1023 0 1023 1023), good := (rows 867 867 871 875 883 867 867 867 867 867) },{ target := 8, region := (rows 1023 1023 4 8 16 1023 1023 1023 0 1023), good := (rows 739 739 743 747 755 739 739 739 739 739) }] }

theorem profile0_node2 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,96] 6 896 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,96] 6 896 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 10 := { lost := (rows 896 832 32 32 32 0 0 0 0 0), upper := (rows 97 162 964 968 976 32 64 128 256 512), lower := (rows 97 162 4 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 1023 1023 1023 0 1023 1023 1023 1023), good := (rows 989 990 988 988 988 988 988 988 988 988) },{ target := 6, region := (rows 1 1023 4 8 16 1023 0 1023 1023 1023), good := (rows 931 930 934 938 946 930 930 930 930 930) },{ target := 7, region := (rows 1023 2 4 8 16 1023 1023 0 1023 1023), good := (rows 865 867 869 873 881 865 865 865 865 865) },{ target := 8, region := (rows 1023 1023 4 8 16 1023 1023 1023 0 1023), good := (rows 739 739 743 747 755 739 739 739 739 739) },{ target := 9, region := (rows 1023 1023 4 8 16 1023 1023 1023 1023 0), good := (rows 483 483 487 491 499 483 483 483 483 483) }] }

theorem profile0_node3 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,160] 6 960 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,160] 6 960 profile0_node3_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 10 := { lost := (rows 384 96 384 96 96 0 0 0 0 0), upper := (rows 97 386 100 904 912 32 64 128 256 512), lower := (rows 97 386 100 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 1023 4 1023 1023 0 1023 1023 1023 1023), good := (rows 987 986 990 986 986 986 986 986 986 986) },{ target := 6, region := (rows 1 1023 4 1023 1023 1023 0 1023 1023 1023), good := (rows 955 954 958 954 954 954 954 954 954 954) },{ target := 7, region := (rows 1023 2 1023 8 16 1023 1023 0 1023 1023), good := (rows 869 871 869 877 885 869 869 869 869 869) },{ target := 8, region := (rows 1023 2 1023 8 16 1023 1023 1023 0 1023), good := (rows 741 743 741 749 757 741 741 741 741 741) }] }

theorem profile0_node5 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,96] 6 896 profile0_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,96] 6 896 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 10 := { lost := (rows 384 96 320 160 160 0 0 0 0 0), upper := (rows 97 386 164 840 848 32 64 128 256 512), lower := (rows 97 386 164 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 1023 4 1023 1023 0 1023 1023 1023 1023), good := (rows 987 986 990 986 986 986 986 986 986 986) },{ target := 6, region := (rows 1 1023 1023 8 16 1023 0 1023 1023 1023), good := (rows 935 934 934 942 950 934 934 934 934 934) },{ target := 7, region := (rows 1023 2 4 1023 1023 1023 1023 0 1023 1023), good := (rows 889 891 893 889 889 889 889 889 889 889) },{ target := 8, region := (rows 1023 2 1023 8 16 1023 1023 1023 0 1023), good := (rows 741 743 741 749 757 741 741 741 741 741) }] }

theorem profile0_node6 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,160] 6 832 profile0_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,160] 6 832 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : CutBound 10 := { lost := (rows 384 96 96 384 384 0 0 0 0 0), upper := (rows 97 386 388 616 624 32 64 128 256 512), lower := (rows 97 386 388 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 1023 1023 8 16 0 1023 1023 1023 1023), good := (rows 967 966 966 974 982 966 966 966 966 966) },{ target := 6, region := (rows 1 1023 1023 8 16 1023 0 1023 1023 1023), good := (rows 935 934 934 942 950 934 934 934 934 934) },{ target := 7, region := (rows 1023 2 4 1023 1023 1023 1023 0 1023 1023), good := (rows 889 891 893 889 889 889 889 889 889 889) },{ target := 8, region := (rows 1023 2 4 1023 1023 1023 1023 1023 0 1023), good := (rows 761 763 765 761 761 761 761 761 761 761) }] }

theorem profile0_node7 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,384] 6 608 profile0_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,384] 6 608 profile0_node7_cert).mp (by decide +kernel))

def profile0_node8_cert : CutBound 10 := { lost := (rows 384 96 448 32 32 0 0 0 0 0), upper := (rows 97 386 548 968 976 32 64 128 256 512), lower := (rows 97 386 548 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 1023 4 1023 1023 0 1023 1023 1023 1023), good := (rows 987 986 990 986 986 986 986 986 986 986) },{ target := 6, region := (rows 1 1023 1023 8 16 1023 0 1023 1023 1023), good := (rows 935 934 934 942 950 934 934 934 934 934) },{ target := 7, region := (rows 1023 2 1023 8 16 1023 1023 0 1023 1023), good := (rows 869 871 869 877 885 869 869 869 869 869) },{ target := 8, region := (rows 1023 2 1023 8 16 1023 1023 1023 0 1023), good := (rows 741 743 741 749 757 741 741 741 741 741) }] }

theorem profile0_node8 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,544] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,544] 6 960 profile0_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,544] 6 960 profile0_node8_cert).mp (by decide +kernel))

def profile0_node9_cert : CutBound 10 := { lost := (rows 384 96 352 128 128 0 0 0 0 0), upper := (rows 97 386 644 872 880 32 64 128 256 512), lower := (rows 97 386 644 8 16 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 1023 1023 8 16 0 1023 1023 1023 1023), good := (rows 967 966 966 974 982 966 966 966 966 966) },{ target := 6, region := (rows 1 1023 1023 8 16 1023 0 1023 1023 1023), good := (rows 935 934 934 942 950 934 934 934 934 934) },{ target := 7, region := (rows 1023 2 4 1023 1023 1023 1023 0 1023 1023), good := (rows 889 891 893 889 889 889 889 889 889 889) },{ target := 8, region := (rows 1023 2 1023 8 16 1023 1023 1023 0 1023), good := (rows 741 743 741 749 757 741 741 741 741 741) }] }

theorem profile0_node9 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,640] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,640] 6 864 profile0_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384,640] 6 864 profile0_node9_cert).mp (by decide +kernel))

def profile0_node4_column : Nat → Fin 10 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | _ => 0

def profile0_node4_route : Route 10 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 768 => (640,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile0_node4 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96,384] 6 (by decide) (choices 2) [96,160,384,544,640] profile0_node4_route profile0_node4_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7
  · exact profile0_node8
  · exact profile0_node9

def profile0_node1_column : Nat → Fin 10 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | _ => 0

def profile0_node1_route : Route 10 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 544 => (160,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | 576 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 9 | 9 => 7 | _ => i)) | 640 => (384,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 768 => (384,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [96] 6 (by decide) (choices 2) [96,160,384] profile0_node1_route profile0_node1_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4

def profile0_node0_column : Nat → Fin 10 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | _ => 0

def profile0_node0_route : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 544 => (96,(fun i => match i.val with | 6 => 9 | 9 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 576 => (96,(fun i => match i.val with | 5 => 9 | 9 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | 640 => (96,(fun i => match i.val with | 5 => 7 | 6 => 9 | 7 => 5 | 9 => 6 | _ => i)) | 768 => (96,(fun i => match i.val with | 5 => 8 | 6 => 9 | 8 => 5 | 9 => 6 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [] 6 (by decide) (choices 2) [96] profile0_node0_route profile0_node0_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=10) [32,32,32,32,32,2,2,2,2,2]) (R (n:=10) [32,32,32,32,32,2,2,2,2,2]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite10
