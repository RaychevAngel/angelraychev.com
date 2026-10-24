import IrregularTen14Base

namespace Delivery.IrregularTen14.Case30
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 259 14 28 752 736 736 736 992 736), lower := (rows 49 259 14 28 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [48,257,10,20] 13 :=
  bound_sound D R [48,257,10,20] 13 bound_2
    ((Boolean.boundCheck_true D R [48,257,10,20] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 259 14 56 724 740 708 708 964 708), lower := (rows 49 259 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [48,257,10,48] 13 :=
  bound_sound D R [48,257,10,48] 13 bound_3
    ((Boolean.boundCheck_true D R [48,257,10,48] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 259 14 76 752 752 752 752 1008 752), lower := (rows 49 259 14 76 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [48,257,10,68] 13 :=
  bound_sound D R [48,257,10,68] 13 bound_4
    ((Boolean.boundCheck_true D R [48,257,10,68] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 259 14 88 756 740 740 740 996 740), lower := (rows 49 259 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [48,257,10,80] 13 :=
  bound_sound D R [48,257,10,80] 13 bound_5
    ((Boolean.boundCheck_true D R [48,257,10,80] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 259 14 200 756 756 756 756 1012 756), lower := (rows 49 259 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [48,257,10,192] 13 :=
  bound_sound D R [48,257,10,192] 13 bound_6
    ((Boolean.boundCheck_true D R [48,257,10,192] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 259 14 524 48 240 208 208 464 720), lower := (rows 49 259 14 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 11 16 0 81 145 273 529), good := (rows 991 975 14 524 976 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [48,257,10,516,32] 13 :=
  bound_sound D R [48,257,10,516,32] 13 bound_8
    ((Boolean.boundCheck_true D R [48,257,10,516,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 259 14 524 80 48 224 224 480 736), lower := (rows 49 259 14 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 11 0 32 97 161 289 545), good := (rows 1007 975 14 524 64 992 64 128 256 512) }] }

theorem upper_10 : Upper D R [48,257,10,516,64,16] 13 :=
  bound_sound D R [48,257,10,516,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [48,257,10,516,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 259 14 524 80 96 240 176 432 688), lower := (rows 49 259 14 524 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 3 7 11 16 32 0 129 257 513), good := (rows 959 911 14 524 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [48,257,10,516,64,64] 13 :=
  bound_sound D R [48,257,10,516,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [48,257,10,516,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 259 14 524 80 160 80 224 480 736), lower := (rows 49 259 14 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 9 0 241 64 208 336 592), good := (rows 943 303 14 524 992 160 992 160 256 512) }] }

theorem upper_13 : Upper D R [48,257,10,516,64,128,16] 13 :=
  bound_sound D R [48,257,10,516,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [48,257,10,516,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 259 14 524 80 160 96 208 464 720), lower := (rows 49 259 14 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 9 80 0 64 208 336 592), good := (rows 927 271 14 524 976 128 976 128 256 512) }] }

theorem upper_14 : Upper D R [48,257,10,516,64,128,32] 13 :=
  bound_sound D R [48,257,10,516,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [48,257,10,516,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 259 14 524 80 160 192 240 368 624), lower := (rows 49 259 14 524 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 259 14 524 49 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [48,257,10,516,64,128,128] 13 :=
  bound_sound D R [48,257,10,516,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [48,257,10,516,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [48,257,10,516,64,128] 13 := by
  apply routed_branch D R [48,257,10,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,10,516,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [48,257,10,516,64] 13 := by
  apply routed_branch D R [48,257,10,516,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,10,516,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [48,257,10,516] 13 := by
  apply routed_branch D R [48,257,10,516] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,10,516] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def bound_16 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 259 14 536 244 228 228 228 484 740), lower := (rows 49 259 14 536 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [48,257,10,528] 13 :=
  bound_sound D R [48,257,10,528] 13 bound_16
    ((Boolean.boundCheck_true D R [48,257,10,528] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 259 14 584 244 244 244 244 500 756), lower := (rows 49 259 14 584 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [48,257,10,576] 13 :=
  bound_sound D R [48,257,10,576] 13 bound_17
    ((Boolean.boundCheck_true D R [48,257,10,576] 13 bound_17).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [48,257,10] 13 := by
  apply routed_branch D R [48,257,10] 13 (by decide) (choices 2) [20,48,68,80,192,516,528,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,257,10] (choices 2) [20,48,68,80,192,516,528,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_16
  · exact upper_17

def bound_18 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 259 22 748 764 748 748 748 1004 748), lower := (rows 49 259 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [48,257,18] 13 :=
  bound_sound D R [48,257,18] 13 bound_18
    ((Boolean.boundCheck_true D R [48,257,18] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 259 28 750 758 742 742 742 998 742), lower := (rows 49 259 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [48,257,24] 13 :=
  bound_sound D R [48,257,24] 13 bound_19
    ((Boolean.boundCheck_true D R [48,257,24] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 192 240 192 240 0 0 0 0 0 0), upper := (rows 49 259 52 718 734 750 718 718 974 718), lower := (rows 49 259 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [48,257,48] 13 :=
  bound_sound D R [48,257,48] 13 bound_20
    ((Boolean.boundCheck_true D R [48,257,48] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 259 70 764 764 764 764 764 1020 764), lower := (rows 49 259 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [48,257,66] 13 :=
  bound_sound D R [48,257,66] 13 bound_21
    ((Boolean.boundCheck_true D R [48,257,66] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 259 76 766 758 758 758 758 1014 758), lower := (rows 49 259 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [48,257,72] 13 :=
  bound_sound D R [48,257,72] 13 bound_22
    ((Boolean.boundCheck_true D R [48,257,72] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 192 240 160 240 0 0 0 0 0 0), upper := (rows 49 259 84 750 766 750 750 750 1006 750), lower := (rows 49 259 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [48,257,80] 13 :=
  bound_sound D R [48,257,80] 13 bound_23
    ((Boolean.boundCheck_true D R [48,257,80] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 192 240 48 240 0 0 0 0 0 0), upper := (rows 49 259 196 766 766 766 766 766 1022 766), lower := (rows 49 259 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [48,257,192] 13 :=
  bound_sound D R [48,257,192] 13 bound_24
    ((Boolean.boundCheck_true D R [48,257,192] 13 bound_24).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 259 518 28 248 232 232 232 488 744), lower := (rows 49 259 518 28 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [48,257,514,20] 13 :=
  bound_sound D R [48,257,514,20] 13 bound_26
    ((Boolean.boundCheck_true D R [48,257,514,20] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 259 518 56 220 236 204 204 460 716), lower := (rows 49 259 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [48,257,514,48] 13 :=
  bound_sound D R [48,257,514,48] 13 bound_27
    ((Boolean.boundCheck_true D R [48,257,514,48] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 259 518 76 248 248 248 248 504 760), lower := (rows 49 259 518 76 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [48,257,514,68] 13 :=
  bound_sound D R [48,257,514,68] 13 bound_28
    ((Boolean.boundCheck_true D R [48,257,514,68] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 259 518 88 252 236 236 236 492 748), lower := (rows 49 259 518 88 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [48,257,514,80] 13 :=
  bound_sound D R [48,257,514,80] 13 bound_29
    ((Boolean.boundCheck_true D R [48,257,514,80] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 259 518 200 252 252 252 252 508 764), lower := (rows 49 259 518 200 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [48,257,514,192] 13 :=
  bound_sound D R [48,257,514,192] 13 bound_30
    ((Boolean.boundCheck_true D R [48,257,514,192] 13 bound_30).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [48,257,514] 13 := by
  apply routed_branch D R [48,257,514] 13 (by decide) (choices 2) [20,48,68,80,192] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,257,514] (choices 2) [20,48,68,80,192] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30

def bound_33 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 259 524 14 48 240 208 208 464 720), lower := (rows 49 259 524 14 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 11 16 0 81 145 273 529), good := (rows 991 975 524 14 976 0 64 128 256 512) }] }

theorem upper_33 : Upper D R [48,257,520,6,32] 13 :=
  bound_sound D R [48,257,520,6,32] 13 bound_33
    ((Boolean.boundCheck_true D R [48,257,520,6,32] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 259 524 14 80 48 224 224 480 736), lower := (rows 49 259 524 14 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 11 0 32 97 161 289 545), good := (rows 1007 975 524 14 64 992 64 128 256 512) }] }

theorem upper_35 : Upper D R [48,257,520,6,64,16] 13 :=
  bound_sound D R [48,257,520,6,64,16] 13 bound_35
    ((Boolean.boundCheck_true D R [48,257,520,6,64,16] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 259 524 14 80 96 240 176 432 688), lower := (rows 49 259 524 14 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 3 7 11 16 32 0 129 257 513), good := (rows 959 911 524 14 16 32 0 128 256 512) }] }

theorem upper_36 : Upper D R [48,257,520,6,64,64] 13 :=
  bound_sound D R [48,257,520,6,64,64] 13 bound_36
    ((Boolean.boundCheck_true D R [48,257,520,6,64,64] 13 bound_36).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 259 524 14 80 160 80 224 480 736), lower := (rows 49 259 524 14 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 11 0 241 64 208 336 592), good := (rows 943 303 524 14 992 160 992 160 256 512) }] }

theorem upper_38 : Upper D R [48,257,520,6,64,128,16] 13 :=
  bound_sound D R [48,257,520,6,64,128,16] 13 bound_38
    ((Boolean.boundCheck_true D R [48,257,520,6,64,128,16] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 259 524 14 80 160 96 208 464 720), lower := (rows 49 259 524 14 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 5 11 80 0 64 208 336 592), good := (rows 927 271 524 14 976 128 976 128 256 512) }] }

theorem upper_39 : Upper D R [48,257,520,6,64,128,32] 13 :=
  bound_sound D R [48,257,520,6,64,128,32] 13 bound_39
    ((Boolean.boundCheck_true D R [48,257,520,6,64,128,32] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 259 524 14 80 160 192 240 368 624), lower := (rows 49 259 524 14 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 259 524 14 49 160 160 160 256 512) }] }

theorem upper_40 : Upper D R [48,257,520,6,64,128,128] 13 :=
  bound_sound D R [48,257,520,6,64,128,128] 13 bound_40
    ((Boolean.boundCheck_true D R [48,257,520,6,64,128,128] 13 bound_40).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => (mask,id))

theorem upper_37 : Upper D R [48,257,520,6,64,128] 13 := by
  apply routed_branch D R [48,257,520,6,64,128] 13 (by decide) (choices 1) [16,32,128] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,520,6,64,128] (choices 1) [16,32,128] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40

def route_34 : Route 10 := (fun mask => (mask,id))

theorem upper_34 : Upper D R [48,257,520,6,64] 13 := by
  apply routed_branch D R [48,257,520,6,64] 13 (by decide) (choices 1) [16,64,128] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,520,6,64] (choices 1) [16,64,128] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37

def route_32 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_32 : Upper D R [48,257,520,6] 13 := by
  apply routed_branch D R [48,257,520,6] 13 (by decide) (choices 1) [32,64] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,257,520,6] (choices 1) [32,64] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_33
  · exact upper_34

def bound_41 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 259 524 26 244 228 228 228 484 740), lower := (rows 49 259 524 26 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [48,257,520,18] 13 :=
  bound_sound D R [48,257,520,18] 13 bound_41
    ((Boolean.boundCheck_true D R [48,257,520,18] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 259 524 28 242 226 226 226 482 738), lower := (rows 49 259 524 28 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [48,257,520,20] 13 :=
  bound_sound D R [48,257,520,20] 13 bound_42
    ((Boolean.boundCheck_true D R [48,257,520,20] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 259 524 56 214 230 198 198 454 710), lower := (rows 49 259 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [48,257,520,48] 13 :=
  bound_sound D R [48,257,520,48] 13 bound_43
    ((Boolean.boundCheck_true D R [48,257,520,48] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 259 524 74 244 244 244 244 500 756), lower := (rows 49 259 524 74 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [48,257,520,66] 13 :=
  bound_sound D R [48,257,520,66] 13 bound_44
    ((Boolean.boundCheck_true D R [48,257,520,66] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 259 524 76 242 242 242 242 498 754), lower := (rows 49 259 524 76 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [48,257,520,68] 13 :=
  bound_sound D R [48,257,520,68] 13 bound_45
    ((Boolean.boundCheck_true D R [48,257,520,68] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 259 524 88 246 230 230 230 486 742), lower := (rows 49 259 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [48,257,520,80] 13 :=
  bound_sound D R [48,257,520,80] 13 bound_46
    ((Boolean.boundCheck_true D R [48,257,520,80] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 259 524 200 246 246 246 246 502 758), lower := (rows 49 259 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [48,257,520,192] 13 :=
  bound_sound D R [48,257,520,192] 13 bound_47
    ((Boolean.boundCheck_true D R [48,257,520,192] 13 bound_47).mp (by decide +kernel))

def route_31 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_31 : Upper D R [48,257,520] 13 := by
  apply routed_branch D R [48,257,520] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192] route_31
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,257,520] (choices 2) [6,18,20,48,66,68,80,192] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_32
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_47

def bound_48 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 259 532 238 254 238 238 238 494 750), lower := (rows 49 259 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [48,257,528] 13 :=
  bound_sound D R [48,257,528] 13 bound_48
    ((Boolean.boundCheck_true D R [48,257,528] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 259 580 254 254 254 254 254 510 766), lower := (rows 49 259 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [48,257,576] 13 :=
  bound_sound D R [48,257,576] 13 bound_49
    ((Boolean.boundCheck_true D R [48,257,576] 13 bound_49).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [48,257] 13 := by
  apply routed_branch D R [48,257] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192,514,520,528,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,257] (choices 2) [10,18,24,48,66,72,80,192,514,520,528,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_18
  · exact upper_19
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_31
  · exact upper_48
  · exact upper_49

theorem upper : Upper D R [48,257] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case30
