import IrregularTen14Base

namespace Delivery.IrregularTen14.Case47
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 35 14 28 752 736 736 736 992 736), lower := (rows 273 35 14 28 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,33,10,20] 13 :=
  bound_sound D R [272,33,10,20] 13 bound_2
    ((Boolean.boundCheck_true D R [272,33,10,20] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 35 14 44 720 752 720 720 976 720), lower := (rows 273 35 14 44 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,33,10,36] 13 :=
  bound_sound D R [272,33,10,36] 13 bound_3
    ((Boolean.boundCheck_true D R [272,33,10,36] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 35 14 56 724 740 708 708 964 708), lower := (rows 273 35 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [272,33,10,48] 13 :=
  bound_sound D R [272,33,10,48] 13 bound_4
    ((Boolean.boundCheck_true D R [272,33,10,48] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 35 14 76 752 752 752 752 1008 752), lower := (rows 273 35 14 76 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [272,33,10,68] 13 :=
  bound_sound D R [272,33,10,68] 13 bound_5
    ((Boolean.boundCheck_true D R [272,33,10,68] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 35 14 88 756 740 740 740 996 740), lower := (rows 273 35 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [272,33,10,80] 13 :=
  bound_sound D R [272,33,10,80] 13 bound_6
    ((Boolean.boundCheck_true D R [272,33,10,80] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 35 14 104 724 756 724 724 980 724), lower := (rows 273 35 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [272,33,10,96] 13 :=
  bound_sound D R [272,33,10,96] 13 bound_7
    ((Boolean.boundCheck_true D R [272,33,10,96] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 35 14 200 756 756 756 756 1012 756), lower := (rows 273 35 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [272,33,10,192] 13 :=
  bound_sound D R [272,33,10,192] 13 bound_8
    ((Boolean.boundCheck_true D R [272,33,10,192] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 273 35 14 524 48 240 208 208 464 720), lower := (rows 273 35 14 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 6 10 16 0 81 145 273 529), good := (rows 977 975 14 524 977 0 64 128 256 512) }] }

theorem upper_10 : Upper D R [272,33,10,516,32] 13 :=
  bound_sound D R [272,33,10,516,32] 13 bound_10
    ((Boolean.boundCheck_true D R [272,33,10,516,32] 13 bound_10).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 48 224 224 480 736), lower := (rows 273 35 14 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 6 14 0 32 98 162 290 546), good := (rows 257 1007 974 524 64 992 64 128 256 512) }] }

theorem upper_12 : Upper D R [272,33,10,516,64,16] 13 :=
  bound_sound D R [272,33,10,516,64,16] 13 bound_12
    ((Boolean.boundCheck_true D R [272,33,10,516,64,16] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 96 240 176 432 688), lower := (rows 273 35 14 524 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 112 64 128 256 512), good := (rows 291 35 14 524 96 96 96 128 256 512) }] }

theorem upper_13 : Upper D R [272,33,10,516,64,64] 13 :=
  bound_sound D R [272,33,10,516,64,64] 13 bound_13
    ((Boolean.boundCheck_true D R [272,33,10,516,64,64] 13 bound_13).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 160 80 224 480 736), lower := (rows 273 35 14 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 9 0 241 64 208 336 592), good := (rows 943 47 14 524 992 160 992 160 256 512) }] }

theorem upper_15 : Upper D R [272,33,10,516,64,128,16] 13 :=
  bound_sound D R [272,33,10,516,64,128,16] 13 bound_15
    ((Boolean.boundCheck_true D R [272,33,10,516,64,128,16] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 160 96 208 464 720), lower := (rows 273 35 14 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 3 14 524 977 128 977 128 256 512) }] }

theorem upper_16 : Upper D R [272,33,10,516,64,128,32] 13 :=
  bound_sound D R [272,33,10,516,64,128,32] 13 bound_16
    ((Boolean.boundCheck_true D R [272,33,10,516,64,128,32] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 160 192 144 352 608), lower := (rows 273 35 14 524 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 6 14 0 224 224 128 498 754), good := (rows 769 879 782 524 864 992 992 992 256 512) }] }

theorem upper_18 : Upper D R [272,33,10,516,64,128,128,16] 13 :=
  bound_sound D R [272,33,10,516,64,128,128,16] 13 bound_18
    ((Boolean.boundCheck_true D R [272,33,10,516,64,128,128,16] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 160 192 160 336 592), lower := (rows 273 35 14 524 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 1023 1023 1023 256 512), good := (rows 483 227 238 748 224 224 224 224 480 736) }] }

theorem upper_19 : Upper D R [272,33,10,516,64,128,128,32] 13 :=
  bound_sound D R [272,33,10,516,64,128,128,32] 13 bound_19
    ((Boolean.boundCheck_true D R [272,33,10,516,64,128,128,32] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 14 524 80 160 192 192 304 560), lower := (rows 273 35 14 524 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 1023 1023 1023 256 512), good := (rows 483 227 238 748 224 224 224 224 480 736) }] }

theorem upper_20 : Upper D R [272,33,10,516,64,128,128,64] 13 :=
  bound_sound D R [272,33,10,516,64,128,128,64] 13 bound_20
    ((Boolean.boundCheck_true D R [272,33,10,516,64,128,128,64] 13 bound_20).mp (by decide +kernel))

def route_17 : Route 10 := (fun mask => (mask,id))

theorem upper_17 : Upper D R [272,33,10,516,64,128,128] 13 := by
  apply routed_branch D R [272,33,10,516,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_17
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,10,516,64,128,128] (choices 1) [16,32,64] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_18
  · exact upper_19
  · exact upper_20

def route_14 : Route 10 := (fun mask => (mask,id))

theorem upper_14 : Upper D R [272,33,10,516,64,128] 13 := by
  apply routed_branch D R [272,33,10,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_14
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,10,516,64,128] (choices 1) [16,32,128] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17

def route_11 : Route 10 := (fun mask => (mask,id))

theorem upper_11 : Upper D R [272,33,10,516,64] 13 := by
  apply routed_branch D R [272,33,10,516,64] 13 (by decide) (choices 1) [16,64,128] route_11
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,10,516,64] (choices 1) [16,64,128] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14

def route_9 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [272,33,10,516] 13 := by
  apply routed_branch D R [272,33,10,516] 13 (by decide) (choices 1) [32,64] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,10,516] (choices 1) [32,64] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def bound_21 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 35 14 536 244 228 228 228 484 740), lower := (rows 273 35 14 536 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [272,33,10,528] 13 :=
  bound_sound D R [272,33,10,528] 13 bound_21
    ((Boolean.boundCheck_true D R [272,33,10,528] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 35 14 552 212 244 212 212 468 724), lower := (rows 273 35 14 552 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [272,33,10,544] 13 :=
  bound_sound D R [272,33,10,544] 13 bound_22
    ((Boolean.boundCheck_true D R [272,33,10,544] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 35 14 584 244 244 244 244 500 756), lower := (rows 273 35 14 584 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [272,33,10,576] 13 :=
  bound_sound D R [272,33,10,576] 13 bound_23
    ((Boolean.boundCheck_true D R [272,33,10,576] 13 bound_23).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,33,10] 13 := by
  apply routed_branch D R [272,33,10] 13 (by decide) (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,33,10] (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_9
  · exact upper_21
  · exact upper_22
  · exact upper_23

def bound_24 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 35 22 748 764 748 748 748 1004 748), lower := (rows 273 35 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [272,33,18] 13 :=
  bound_sound D R [272,33,18] 13 bound_24
    ((Boolean.boundCheck_true D R [272,33,18] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 35 28 750 758 742 742 742 998 742), lower := (rows 273 35 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [272,33,24] 13 :=
  bound_sound D R [272,33,24] 13 bound_25
    ((Boolean.boundCheck_true D R [272,33,24] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 35 38 732 732 764 732 732 988 732), lower := (rows 273 35 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [272,33,34] 13 :=
  bound_sound D R [272,33,34] 13 bound_26
    ((Boolean.boundCheck_true D R [272,33,34] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 35 44 734 726 758 726 726 982 726), lower := (rows 273 35 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [272,33,40] 13 :=
  bound_sound D R [272,33,40] 13 bound_27
    ((Boolean.boundCheck_true D R [272,33,40] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 273 35 52 718 734 750 718 718 974 718), lower := (rows 273 35 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [272,33,48] 13 :=
  bound_sound D R [272,33,48] 13 bound_28
    ((Boolean.boundCheck_true D R [272,33,48] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 35 70 764 764 764 764 764 1020 764), lower := (rows 273 35 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [272,33,66] 13 :=
  bound_sound D R [272,33,66] 13 bound_29
    ((Boolean.boundCheck_true D R [272,33,66] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 35 76 766 758 758 758 758 1014 758), lower := (rows 273 35 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [272,33,72] 13 :=
  bound_sound D R [272,33,72] 13 bound_30
    ((Boolean.boundCheck_true D R [272,33,72] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 273 35 84 750 766 750 750 750 1006 750), lower := (rows 273 35 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [272,33,80] 13 :=
  bound_sound D R [272,33,80] 13 bound_31
    ((Boolean.boundCheck_true D R [272,33,80] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 273 35 100 734 734 766 734 734 990 734), lower := (rows 273 35 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [272,33,96] 13 :=
  bound_sound D R [272,33,96] 13 bound_32
    ((Boolean.boundCheck_true D R [272,33,96] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 273 35 196 766 766 766 766 766 1022 766), lower := (rows 273 35 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [272,33,192] 13 :=
  bound_sound D R [272,33,192] 13 bound_33
    ((Boolean.boundCheck_true D R [272,33,192] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 35 518 28 248 232 232 232 488 744), lower := (rows 273 35 518 28 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [272,33,514,20] 13 :=
  bound_sound D R [272,33,514,20] 13 bound_35
    ((Boolean.boundCheck_true D R [272,33,514,20] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 35 518 44 216 248 216 216 472 728), lower := (rows 273 35 518 44 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,33,514,36] 13 :=
  bound_sound D R [272,33,514,36] 13 bound_36
    ((Boolean.boundCheck_true D R [272,33,514,36] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 35 518 56 220 236 204 204 460 716), lower := (rows 273 35 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [272,33,514,48] 13 :=
  bound_sound D R [272,33,514,48] 13 bound_37
    ((Boolean.boundCheck_true D R [272,33,514,48] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 35 518 76 248 248 248 248 504 760), lower := (rows 273 35 518 76 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [272,33,514,68] 13 :=
  bound_sound D R [272,33,514,68] 13 bound_38
    ((Boolean.boundCheck_true D R [272,33,514,68] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 35 518 88 252 236 236 236 492 748), lower := (rows 273 35 518 88 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [272,33,514,80] 13 :=
  bound_sound D R [272,33,514,80] 13 bound_39
    ((Boolean.boundCheck_true D R [272,33,514,80] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 35 518 104 220 252 220 220 476 732), lower := (rows 273 35 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [272,33,514,96] 13 :=
  bound_sound D R [272,33,514,96] 13 bound_40
    ((Boolean.boundCheck_true D R [272,33,514,96] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 35 518 200 252 252 252 252 508 764), lower := (rows 273 35 518 200 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [272,33,514,192] 13 :=
  bound_sound D R [272,33,514,192] 13 bound_41
    ((Boolean.boundCheck_true D R [272,33,514,192] 13 bound_41).mp (by decide +kernel))

def route_34 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_34 : Upper D R [272,33,514] 13 := by
  apply routed_branch D R [272,33,514] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_34
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,33,514] (choices 2) [20,36,48,68,80,96,192] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37
  · exact upper_38
  · exact upper_39
  · exact upper_40
  · exact upper_41

def bound_44 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 273 35 524 14 48 240 208 208 464 720), lower := (rows 273 35 524 14 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 6 10 16 0 81 145 273 529), good := (rows 977 975 524 14 977 0 64 128 256 512) }] }

theorem upper_44 : Upper D R [272,33,520,6,32] 13 :=
  bound_sound D R [272,33,520,6,32] 13 bound_44
    ((Boolean.boundCheck_true D R [272,33,520,6,32] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 48 224 224 480 736), lower := (rows 273 35 524 14 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 14 10 0 32 98 162 290 546), good := (rows 257 1007 524 974 64 992 64 128 256 512) }] }

theorem upper_46 : Upper D R [272,33,520,6,64,16] 13 :=
  bound_sound D R [272,33,520,6,64,16] 13 bound_46
    ((Boolean.boundCheck_true D R [272,33,520,6,64,16] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 96 240 176 432 688), lower := (rows 273 35 524 14 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 112 64 128 256 512), good := (rows 291 35 524 14 96 96 96 128 256 512) }] }

theorem upper_47 : Upper D R [272,33,520,6,64,64] 13 :=
  bound_sound D R [272,33,520,6,64,64] 13 bound_47
    ((Boolean.boundCheck_true D R [272,33,520,6,64,64] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 160 80 224 480 736), lower := (rows 273 35 524 14 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 11 0 241 64 208 336 592), good := (rows 943 47 524 14 992 160 992 160 256 512) }] }

theorem upper_49 : Upper D R [272,33,520,6,64,128,16] 13 :=
  bound_sound D R [272,33,520,6,64,128,16] 13 bound_49
    ((Boolean.boundCheck_true D R [272,33,520,6,64,128,16] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 160 96 208 464 720), lower := (rows 273 35 524 14 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 3 524 14 977 128 977 128 256 512) }] }

theorem upper_50 : Upper D R [272,33,520,6,64,128,32] 13 :=
  bound_sound D R [272,33,520,6,64,128,32] 13 bound_50
    ((Boolean.boundCheck_true D R [272,33,520,6,64,128,32] 13 bound_50).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 160 192 144 352 608), lower := (rows 273 35 524 14 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 14 10 0 224 224 128 498 754), good := (rows 769 879 524 782 864 992 992 992 256 512) }] }

theorem upper_52 : Upper D R [272,33,520,6,64,128,128,16] 13 :=
  bound_sound D R [272,33,520,6,64,128,128,16] 13 bound_52
    ((Boolean.boundCheck_true D R [272,33,520,6,64,128,128,16] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 160 192 160 336 592), lower := (rows 273 35 524 14 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 1023 1023 1023 256 512), good := (rows 483 227 748 238 224 224 224 224 480 736) }] }

theorem upper_53 : Upper D R [272,33,520,6,64,128,128,32] 13 :=
  bound_sound D R [272,33,520,6,64,128,128,32] 13 bound_53
    ((Boolean.boundCheck_true D R [272,33,520,6,64,128,128,32] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 35 524 14 80 160 192 192 304 560), lower := (rows 273 35 524 14 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 1023 1023 1023 256 512), good := (rows 483 227 748 238 224 224 224 224 480 736) }] }

theorem upper_54 : Upper D R [272,33,520,6,64,128,128,64] 13 :=
  bound_sound D R [272,33,520,6,64,128,128,64] 13 bound_54
    ((Boolean.boundCheck_true D R [272,33,520,6,64,128,128,64] 13 bound_54).mp (by decide +kernel))

def route_51 : Route 10 := (fun mask => (mask,id))

theorem upper_51 : Upper D R [272,33,520,6,64,128,128] 13 := by
  apply routed_branch D R [272,33,520,6,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_51
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,520,6,64,128,128] (choices 1) [16,32,64] route_51).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_52
  · exact upper_53
  · exact upper_54

def route_48 : Route 10 := (fun mask => (mask,id))

theorem upper_48 : Upper D R [272,33,520,6,64,128] 13 := by
  apply routed_branch D R [272,33,520,6,64,128] 13 (by decide) (choices 1) [16,32,128] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,520,6,64,128] (choices 1) [16,32,128] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51

def route_45 : Route 10 := (fun mask => (mask,id))

theorem upper_45 : Upper D R [272,33,520,6,64] 13 := by
  apply routed_branch D R [272,33,520,6,64] 13 (by decide) (choices 1) [16,64,128] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,520,6,64] (choices 1) [16,64,128] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_46
  · exact upper_47
  · exact upper_48

def route_43 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_43 : Upper D R [272,33,520,6] 13 := by
  apply routed_branch D R [272,33,520,6] 13 (by decide) (choices 1) [32,64] route_43
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,33,520,6] (choices 1) [32,64] route_43).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_44
  · exact upper_45

def bound_55 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 35 524 26 244 228 228 228 484 740), lower := (rows 273 35 524 26 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [272,33,520,18] 13 :=
  bound_sound D R [272,33,520,18] 13 bound_55
    ((Boolean.boundCheck_true D R [272,33,520,18] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 35 524 28 242 226 226 226 482 738), lower := (rows 273 35 524 28 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [272,33,520,20] 13 :=
  bound_sound D R [272,33,520,20] 13 bound_56
    ((Boolean.boundCheck_true D R [272,33,520,20] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 35 524 42 212 244 212 212 468 724), lower := (rows 273 35 524 42 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [272,33,520,34] 13 :=
  bound_sound D R [272,33,520,34] 13 bound_57
    ((Boolean.boundCheck_true D R [272,33,520,34] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 35 524 44 210 242 210 210 466 722), lower := (rows 273 35 524 44 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [272,33,520,36] 13 :=
  bound_sound D R [272,33,520,36] 13 bound_58
    ((Boolean.boundCheck_true D R [272,33,520,36] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 35 524 56 214 230 198 198 454 710), lower := (rows 273 35 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [272,33,520,48] 13 :=
  bound_sound D R [272,33,520,48] 13 bound_59
    ((Boolean.boundCheck_true D R [272,33,520,48] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 35 524 74 244 244 244 244 500 756), lower := (rows 273 35 524 74 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [272,33,520,66] 13 :=
  bound_sound D R [272,33,520,66] 13 bound_60
    ((Boolean.boundCheck_true D R [272,33,520,66] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 35 524 76 242 242 242 242 498 754), lower := (rows 273 35 524 76 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [272,33,520,68] 13 :=
  bound_sound D R [272,33,520,68] 13 bound_61
    ((Boolean.boundCheck_true D R [272,33,520,68] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 35 524 88 246 230 230 230 486 742), lower := (rows 273 35 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [272,33,520,80] 13 :=
  bound_sound D R [272,33,520,80] 13 bound_62
    ((Boolean.boundCheck_true D R [272,33,520,80] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 35 524 104 214 246 214 214 470 726), lower := (rows 273 35 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [272,33,520,96] 13 :=
  bound_sound D R [272,33,520,96] 13 bound_63
    ((Boolean.boundCheck_true D R [272,33,520,96] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 35 524 200 246 246 246 246 502 758), lower := (rows 273 35 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [272,33,520,192] 13 :=
  bound_sound D R [272,33,520,192] 13 bound_64
    ((Boolean.boundCheck_true D R [272,33,520,192] 13 bound_64).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_42 : Upper D R [272,33,520] 13 := by
  apply routed_branch D R [272,33,520] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_42
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,33,520] (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_43
  · exact upper_55
  · exact upper_56
  · exact upper_57
  · exact upper_58
  · exact upper_59
  · exact upper_60
  · exact upper_61
  · exact upper_62
  · exact upper_63
  · exact upper_64

def bound_65 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 35 532 238 254 238 238 238 494 750), lower := (rows 273 35 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [272,33,528] 13 :=
  bound_sound D R [272,33,528] 13 bound_65
    ((Boolean.boundCheck_true D R [272,33,528] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 35 548 222 222 254 222 222 478 734), lower := (rows 273 35 548 8 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [272,33,544] 13 :=
  bound_sound D R [272,33,544] 13 bound_66
    ((Boolean.boundCheck_true D R [272,33,544] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 35 580 254 254 254 254 254 510 766), lower := (rows 273 35 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [272,33,576] 13 :=
  bound_sound D R [272,33,576] 13 bound_67
    ((Boolean.boundCheck_true D R [272,33,576] 13 bound_67).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,33] 13 := by
  apply routed_branch D R [272,33] 13 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96,192,514,520,528,544,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,33] (choices 2) [10,18,24,34,40,48,66,72,80,96,192,514,520,528,544,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_42
  · exact upper_65
  · exact upper_66
  · exact upper_67

theorem upper : Upper D R [272,33] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case47
