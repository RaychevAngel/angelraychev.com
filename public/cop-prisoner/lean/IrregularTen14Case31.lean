import IrregularTen14Base

namespace Delivery.IrregularTen14.Case31
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 7 56 728 744 712 712 968 712), lower := (rows 49 262 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [48,260,3,48] 13 :=
  bound_sound D R [48,260,3,48] 13 bound_2
    ((Boolean.boundCheck_true D R [48,260,3,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 7 88 760 744 744 744 1000 744), lower := (rows 49 262 7 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [48,260,3,80] 13 :=
  bound_sound D R [48,260,3,80] 13 bound_3
    ((Boolean.boundCheck_true D R [48,260,3,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 7 200 760 760 760 760 1016 760), lower := (rows 49 262 7 200 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [48,260,3,192] 13 :=
  bound_sound D R [48,260,3,192] 13 bound_4
    ((Boolean.boundCheck_true D R [48,260,3,192] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 7 536 248 232 232 232 488 744), lower := (rows 49 262 7 536 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [48,260,3,528] 13 :=
  bound_sound D R [48,260,3,528] 13 bound_5
    ((Boolean.boundCheck_true D R [48,260,3,528] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 7 584 248 248 248 248 504 760), lower := (rows 49 262 7 584 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [48,260,3,576] 13 :=
  bound_sound D R [48,260,3,576] 13 bound_6
    ((Boolean.boundCheck_true D R [48,260,3,576] 13 bound_6).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [48,260,3] 13 := by
  apply routed_branch D R [48,260,3] 13 (by decide) (choices 2) [48,80,192,528,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,3] (choices 2) [48,80,192,528,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6

def bound_8 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 13 26 752 736 736 736 992 736), lower := (rows 49 262 13 26 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [48,260,9,18] 13 :=
  bound_sound D R [48,260,9,18] 13 bound_8
    ((Boolean.boundCheck_true D R [48,260,9,18] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 13 56 722 738 706 706 962 706), lower := (rows 49 262 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [48,260,9,48] 13 :=
  bound_sound D R [48,260,9,48] 13 bound_9
    ((Boolean.boundCheck_true D R [48,260,9,48] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 13 74 752 752 752 752 1008 752), lower := (rows 49 262 13 74 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [48,260,9,66] 13 :=
  bound_sound D R [48,260,9,66] 13 bound_10
    ((Boolean.boundCheck_true D R [48,260,9,66] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 13 88 754 738 738 738 994 738), lower := (rows 49 262 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [48,260,9,80] 13 :=
  bound_sound D R [48,260,9,80] 13 bound_11
    ((Boolean.boundCheck_true D R [48,260,9,80] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 13 200 754 754 754 754 1010 754), lower := (rows 49 262 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [48,260,9,192] 13 :=
  bound_sound D R [48,260,9,192] 13 bound_12
    ((Boolean.boundCheck_true D R [48,260,9,192] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 13 522 48 240 208 208 464 720), lower := (rows 49 262 13 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 7 5 13 16 0 81 145 273 529), good := (rows 991 270 975 522 976 0 64 128 256 512) }] }

theorem upper_14 : Upper D R [48,260,9,514,32] 13 :=
  bound_sound D R [48,260,9,514,32] 13 bound_14
    ((Boolean.boundCheck_true D R [48,260,9,514,32] 13 bound_14).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 13 522 80 48 224 224 480 736), lower := (rows 49 262 13 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 13 0 32 97 161 289 545), good := (rows 1007 270 975 522 64 992 64 128 256 512) }] }

theorem upper_16 : Upper D R [48,260,9,514,64,16] 13 :=
  bound_sound D R [48,260,9,514,64,16] 13 bound_16
    ((Boolean.boundCheck_true D R [48,260,9,514,64,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 262 13 522 80 96 240 176 432 688), lower := (rows 49 262 13 522 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 7 5 13 16 32 0 129 257 513), good := (rows 959 270 911 522 16 32 0 128 256 512) }] }

theorem upper_17 : Upper D R [48,260,9,514,64,64] 13 :=
  bound_sound D R [48,260,9,514,64,64] 13 bound_17
    ((Boolean.boundCheck_true D R [48,260,9,514,64,64] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 13 522 80 160 80 224 480 736), lower := (rows 49 262 13 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 9 0 241 64 208 336 592), good := (rows 943 262 47 522 992 160 992 160 256 512) }] }

theorem upper_19 : Upper D R [48,260,9,514,64,128,16] 13 :=
  bound_sound D R [48,260,9,514,64,128,16] 13 bound_19
    ((Boolean.boundCheck_true D R [48,260,9,514,64,128,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 13 522 80 160 96 208 464 720), lower := (rows 49 262 13 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 5 9 80 0 64 208 336 592), good := (rows 927 262 15 522 976 128 976 128 256 512) }] }

theorem upper_20 : Upper D R [48,260,9,514,64,128,32] 13 :=
  bound_sound D R [48,260,9,514,64,128,32] 13 bound_20
    ((Boolean.boundCheck_true D R [48,260,9,514,64,128,32] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 262 13 522 80 160 192 240 368 624), lower := (rows 49 262 13 522 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 262 13 522 49 160 160 160 256 512) }] }

theorem upper_21 : Upper D R [48,260,9,514,64,128,128] 13 :=
  bound_sound D R [48,260,9,514,64,128,128] 13 bound_21
    ((Boolean.boundCheck_true D R [48,260,9,514,64,128,128] 13 bound_21).mp (by decide +kernel))

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [48,260,9,514,64,128] 13 := by
  apply routed_branch D R [48,260,9,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,9,514,64,128] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [48,260,9,514,64] 13 := by
  apply routed_branch D R [48,260,9,514,64] 13 (by decide) (choices 1) [16,64,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,9,514,64] (choices 1) [16,64,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_13 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_13 : Upper D R [48,260,9,514] 13 := by
  apply routed_branch D R [48,260,9,514] 13 (by decide) (choices 1) [32,64] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,9,514] (choices 1) [32,64] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def bound_22 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 13 536 242 226 226 226 482 738), lower := (rows 49 262 13 536 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [48,260,9,528] 13 :=
  bound_sound D R [48,260,9,528] 13 bound_22
    ((Boolean.boundCheck_true D R [48,260,9,528] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 13 584 242 242 242 242 498 754), lower := (rows 49 262 13 584 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [48,260,9,576] 13 :=
  bound_sound D R [48,260,9,576] 13 bound_23
    ((Boolean.boundCheck_true D R [48,260,9,576] 13 bound_23).mp (by decide +kernel))

def route_7 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [48,260,9] 13 := by
  apply routed_branch D R [48,260,9] 13 (by decide) (choices 2) [18,48,66,80,192,514,528,576] route_7
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,9] (choices 2) [18,48,66,80,192,514,528,576] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13
  · exact upper_22
  · exact upper_23

def bound_25 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 14 25 752 736 736 736 992 736), lower := (rows 49 262 14 25 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [48,260,10,17] 13 :=
  bound_sound D R [48,260,10,17] 13 bound_25
    ((Boolean.boundCheck_true D R [48,260,10,17] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 14 56 721 737 705 705 961 705), lower := (rows 49 262 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [48,260,10,48] 13 :=
  bound_sound D R [48,260,10,48] 13 bound_26
    ((Boolean.boundCheck_true D R [48,260,10,48] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 14 73 752 752 752 752 1008 752), lower := (rows 49 262 14 73 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [48,260,10,65] 13 :=
  bound_sound D R [48,260,10,65] 13 bound_27
    ((Boolean.boundCheck_true D R [48,260,10,65] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 14 88 753 737 737 737 993 737), lower := (rows 49 262 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [48,260,10,80] 13 :=
  bound_sound D R [48,260,10,80] 13 bound_28
    ((Boolean.boundCheck_true D R [48,260,10,80] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 14 200 753 753 753 753 1009 753), lower := (rows 49 262 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [48,260,10,192] 13 :=
  bound_sound D R [48,260,10,192] 13 bound_29
    ((Boolean.boundCheck_true D R [48,260,10,192] 13 bound_29).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 14 521 48 240 208 208 464 720), lower := (rows 49 262 14 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 11 13 9 16 0 81 145 273 529), good := (rows 991 262 14 975 976 0 64 128 256 512) }] }

theorem upper_31 : Upper D R [48,260,10,513,32] 13 :=
  bound_sound D R [48,260,10,513,32] 13 bound_31
    ((Boolean.boundCheck_true D R [48,260,10,513,32] 13 bound_31).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 14 521 80 48 224 224 480 736), lower := (rows 49 262 14 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 11 13 9 0 32 97 161 289 545), good := (rows 1007 262 14 975 64 992 64 128 256 512) }] }

theorem upper_33 : Upper D R [48,260,10,513,64,16] 13 :=
  bound_sound D R [48,260,10,513,64,16] 13 bound_33
    ((Boolean.boundCheck_true D R [48,260,10,513,64,16] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 262 14 521 80 96 240 176 432 688), lower := (rows 49 262 14 521 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 11 13 9 16 32 0 129 257 513), good := (rows 959 262 14 911 16 32 0 128 256 512) }] }

theorem upper_34 : Upper D R [48,260,10,513,64,64] 13 :=
  bound_sound D R [48,260,10,513,64,64] 13 bound_34
    ((Boolean.boundCheck_true D R [48,260,10,513,64,64] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 14 521 80 160 80 224 480 736), lower := (rows 49 262 14 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 13 9 0 241 64 208 336 592), good := (rows 943 262 14 559 992 160 992 160 256 512) }] }

theorem upper_36 : Upper D R [48,260,10,513,64,128,16] 13 :=
  bound_sound D R [48,260,10,513,64,128,16] 13 bound_36
    ((Boolean.boundCheck_true D R [48,260,10,513,64,128,16] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 14 521 80 160 96 208 464 720), lower := (rows 49 262 14 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 13 9 80 0 64 208 336 592), good := (rows 927 262 14 527 976 128 976 128 256 512) }] }

theorem upper_37 : Upper D R [48,260,10,513,64,128,32] 13 :=
  bound_sound D R [48,260,10,513,64,128,32] 13 bound_37
    ((Boolean.boundCheck_true D R [48,260,10,513,64,128,32] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 262 14 521 80 160 192 240 368 624), lower := (rows 49 262 14 521 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 262 14 521 49 160 160 160 256 512) }] }

theorem upper_38 : Upper D R [48,260,10,513,64,128,128] 13 :=
  bound_sound D R [48,260,10,513,64,128,128] 13 bound_38
    ((Boolean.boundCheck_true D R [48,260,10,513,64,128,128] 13 bound_38).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => (mask,id))

theorem upper_35 : Upper D R [48,260,10,513,64,128] 13 := by
  apply routed_branch D R [48,260,10,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,10,513,64,128] (choices 1) [16,32,128] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_36
  · exact upper_37
  · exact upper_38

def route_32 : Route 10 := (fun mask => (mask,id))

theorem upper_32 : Upper D R [48,260,10,513,64] 13 := by
  apply routed_branch D R [48,260,10,513,64] 13 (by decide) (choices 1) [16,64,128] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,10,513,64] (choices 1) [16,64,128] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_35

def route_30 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_30 : Upper D R [48,260,10,513] 13 := by
  apply routed_branch D R [48,260,10,513] 13 (by decide) (choices 1) [32,64] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,10,513] (choices 1) [32,64] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_31
  · exact upper_32

def bound_39 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 14 536 241 225 225 225 481 737), lower := (rows 49 262 14 536 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [48,260,10,528] 13 :=
  bound_sound D R [48,260,10,528] 13 bound_39
    ((Boolean.boundCheck_true D R [48,260,10,528] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 14 584 241 241 241 241 497 753), lower := (rows 49 262 14 584 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [48,260,10,576] 13 :=
  bound_sound D R [48,260,10,576] 13 bound_40
    ((Boolean.boundCheck_true D R [48,260,10,576] 13 bound_40).mp (by decide +kernel))

def route_24 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_24 : Upper D R [48,260,10] 13 := by
  apply routed_branch D R [48,260,10] 13 (by decide) (choices 2) [17,48,65,80,192,513,528,576] route_24
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,10] (choices 2) [17,48,65,80,192,513,528,576] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_39
  · exact upper_40

def bound_41 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 262 21 746 762 746 746 746 1002 746), lower := (rows 49 262 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [48,260,17] 13 :=
  bound_sound D R [48,260,17] 13 bound_41
    ((Boolean.boundCheck_true D R [48,260,17] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 262 22 745 761 745 745 745 1001 745), lower := (rows 49 262 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [48,260,18] 13 :=
  bound_sound D R [48,260,18] 13 bound_42
    ((Boolean.boundCheck_true D R [48,260,18] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 262 28 747 755 739 739 739 995 739), lower := (rows 49 262 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [48,260,24] 13 :=
  bound_sound D R [48,260,24] 13 bound_43
    ((Boolean.boundCheck_true D R [48,260,24] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 192 240 192 240 0 0 0 0 0 0), upper := (rows 49 262 52 715 731 747 715 715 971 715), lower := (rows 49 262 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [48,260,48] 13 :=
  bound_sound D R [48,260,48] 13 bound_44
    ((Boolean.boundCheck_true D R [48,260,48] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 262 69 762 762 762 762 762 1018 762), lower := (rows 49 262 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [48,260,65] 13 :=
  bound_sound D R [48,260,65] 13 bound_45
    ((Boolean.boundCheck_true D R [48,260,65] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 262 70 761 761 761 761 761 1017 761), lower := (rows 49 262 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [48,260,66] 13 :=
  bound_sound D R [48,260,66] 13 bound_46
    ((Boolean.boundCheck_true D R [48,260,66] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 262 76 763 755 755 755 755 1011 755), lower := (rows 49 262 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [48,260,72] 13 :=
  bound_sound D R [48,260,72] 13 bound_47
    ((Boolean.boundCheck_true D R [48,260,72] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 192 240 160 240 0 0 0 0 0 0), upper := (rows 49 262 84 747 763 747 747 747 1003 747), lower := (rows 49 262 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [48,260,80] 13 :=
  bound_sound D R [48,260,80] 13 bound_48
    ((Boolean.boundCheck_true D R [48,260,80] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 192 240 48 240 0 0 0 0 0 0), upper := (rows 49 262 196 763 763 763 763 763 1019 763), lower := (rows 49 262 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [48,260,192] 13 :=
  bound_sound D R [48,260,192] 13 bound_49
    ((Boolean.boundCheck_true D R [48,260,192] 13 bound_49).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 517 26 248 232 232 232 488 744), lower := (rows 49 262 517 26 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [48,260,513,18] 13 :=
  bound_sound D R [48,260,513,18] 13 bound_51
    ((Boolean.boundCheck_true D R [48,260,513,18] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 517 56 218 234 202 202 458 714), lower := (rows 49 262 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [48,260,513,48] 13 :=
  bound_sound D R [48,260,513,48] 13 bound_52
    ((Boolean.boundCheck_true D R [48,260,513,48] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 517 74 248 248 248 248 504 760), lower := (rows 49 262 517 74 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [48,260,513,66] 13 :=
  bound_sound D R [48,260,513,66] 13 bound_53
    ((Boolean.boundCheck_true D R [48,260,513,66] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 517 88 250 234 234 234 490 746), lower := (rows 49 262 517 88 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [48,260,513,80] 13 :=
  bound_sound D R [48,260,513,80] 13 bound_54
    ((Boolean.boundCheck_true D R [48,260,513,80] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 517 200 250 250 250 250 506 762), lower := (rows 49 262 517 200 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [48,260,513,192] 13 :=
  bound_sound D R [48,260,513,192] 13 bound_55
    ((Boolean.boundCheck_true D R [48,260,513,192] 13 bound_55).mp (by decide +kernel))

def route_50 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_50 : Upper D R [48,260,513] 13 := by
  apply routed_branch D R [48,260,513] 13 (by decide) (choices 2) [18,48,66,80,192] route_50
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,513] (choices 2) [18,48,66,80,192] route_50).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55

def bound_57 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 518 25 248 232 232 232 488 744), lower := (rows 49 262 518 25 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [48,260,514,17] 13 :=
  bound_sound D R [48,260,514,17] 13 bound_57
    ((Boolean.boundCheck_true D R [48,260,514,17] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 518 56 217 233 201 201 457 713), lower := (rows 49 262 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [48,260,514,48] 13 :=
  bound_sound D R [48,260,514,48] 13 bound_58
    ((Boolean.boundCheck_true D R [48,260,514,48] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 518 73 248 248 248 248 504 760), lower := (rows 49 262 518 73 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [48,260,514,65] 13 :=
  bound_sound D R [48,260,514,65] 13 bound_59
    ((Boolean.boundCheck_true D R [48,260,514,65] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 518 88 249 233 233 233 489 745), lower := (rows 49 262 518 88 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [48,260,514,80] 13 :=
  bound_sound D R [48,260,514,80] 13 bound_60
    ((Boolean.boundCheck_true D R [48,260,514,80] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 518 200 249 249 249 249 505 761), lower := (rows 49 262 518 200 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [48,260,514,192] 13 :=
  bound_sound D R [48,260,514,192] 13 bound_61
    ((Boolean.boundCheck_true D R [48,260,514,192] 13 bound_61).mp (by decide +kernel))

def route_56 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_56 : Upper D R [48,260,514] 13 := by
  apply routed_branch D R [48,260,514] 13 (by decide) (choices 2) [17,48,65,80,192] route_56
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,514] (choices 2) [17,48,65,80,192] route_56).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_57
  · exact upper_58
  · exact upper_59
  · exact upper_60
  · exact upper_61

def bound_64 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 524 11 48 240 208 208 464 720), lower := (rows 49 262 524 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 11 13 9 16 0 81 145 273 529), good := (rows 991 262 526 975 976 0 64 128 256 512) }] }

theorem upper_64 : Upper D R [48,260,520,3,32] 13 :=
  bound_sound D R [48,260,520,3,32] 13 bound_64
    ((Boolean.boundCheck_true D R [48,260,520,3,32] 13 bound_64).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 524 11 80 48 224 224 480 736), lower := (rows 49 262 524 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 11 13 9 0 32 97 161 289 545), good := (rows 1007 262 526 975 64 992 64 128 256 512) }] }

theorem upper_66 : Upper D R [48,260,520,3,64,16] 13 :=
  bound_sound D R [48,260,520,3,64,16] 13 bound_66
    ((Boolean.boundCheck_true D R [48,260,520,3,64,16] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 262 524 11 80 96 240 176 432 688), lower := (rows 49 262 524 11 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 11 13 9 16 32 0 129 257 513), good := (rows 959 262 526 911 16 32 0 128 256 512) }] }

theorem upper_67 : Upper D R [48,260,520,3,64,64] 13 :=
  bound_sound D R [48,260,520,3,64,64] 13 bound_67
    ((Boolean.boundCheck_true D R [48,260,520,3,64,64] 13 bound_67).mp (by decide +kernel))

def bound_69 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 262 524 11 80 160 80 224 480 736), lower := (rows 49 262 524 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 9 0 241 64 208 336 592), good := (rows 943 262 524 47 992 160 992 160 256 512) }] }

theorem upper_69 : Upper D R [48,260,520,3,64,128,16] 13 :=
  bound_sound D R [48,260,520,3,64,128,16] 13 bound_69
    ((Boolean.boundCheck_true D R [48,260,520,3,64,128,16] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 262 524 11 80 160 96 208 464 720), lower := (rows 49 262 524 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 5 9 80 0 64 208 336 592), good := (rows 927 262 524 15 976 128 976 128 256 512) }] }

theorem upper_70 : Upper D R [48,260,520,3,64,128,32] 13 :=
  bound_sound D R [48,260,520,3,64,128,32] 13 bound_70
    ((Boolean.boundCheck_true D R [48,260,520,3,64,128,32] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 262 524 11 80 160 192 240 368 624), lower := (rows 49 262 524 11 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 262 524 11 49 160 160 160 256 512) }] }

theorem upper_71 : Upper D R [48,260,520,3,64,128,128] 13 :=
  bound_sound D R [48,260,520,3,64,128,128] 13 bound_71
    ((Boolean.boundCheck_true D R [48,260,520,3,64,128,128] 13 bound_71).mp (by decide +kernel))

def route_68 : Route 10 := (fun mask => (mask,id))

theorem upper_68 : Upper D R [48,260,520,3,64,128] 13 := by
  apply routed_branch D R [48,260,520,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_68
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,520,3,64,128] (choices 1) [16,32,128] route_68).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_69
  · exact upper_70
  · exact upper_71

def route_65 : Route 10 := (fun mask => (mask,id))

theorem upper_65 : Upper D R [48,260,520,3,64] 13 := by
  apply routed_branch D R [48,260,520,3,64] 13 (by decide) (choices 1) [16,64,128] route_65
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,520,3,64] (choices 1) [16,64,128] route_65).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_66
  · exact upper_67
  · exact upper_68

def route_63 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_63 : Upper D R [48,260,520,3] 13 := by
  apply routed_branch D R [48,260,520,3] 13 (by decide) (choices 1) [32,64] route_63
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,260,520,3] (choices 1) [32,64] route_63).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_64
  · exact upper_65

def bound_72 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 524 25 242 226 226 226 482 738), lower := (rows 49 262 524 25 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [48,260,520,17] 13 :=
  bound_sound D R [48,260,520,17] 13 bound_72
    ((Boolean.boundCheck_true D R [48,260,520,17] 13 bound_72).mp (by decide +kernel))

def bound_73 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 262 524 26 241 225 225 225 481 737), lower := (rows 49 262 524 26 16 32 64 128 256 512), losses := [] }

theorem upper_73 : Upper D R [48,260,520,18] 13 :=
  bound_sound D R [48,260,520,18] 13 bound_73
    ((Boolean.boundCheck_true D R [48,260,520,18] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 262 524 56 211 227 195 195 451 707), lower := (rows 49 262 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_74 : Upper D R [48,260,520,48] 13 :=
  bound_sound D R [48,260,520,48] 13 bound_74
    ((Boolean.boundCheck_true D R [48,260,520,48] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 524 73 242 242 242 242 498 754), lower := (rows 49 262 524 73 16 32 64 128 256 512), losses := [] }

theorem upper_75 : Upper D R [48,260,520,65] 13 :=
  bound_sound D R [48,260,520,65] 13 bound_75
    ((Boolean.boundCheck_true D R [48,260,520,65] 13 bound_75).mp (by decide +kernel))

def bound_76 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 262 524 74 241 241 241 241 497 753), lower := (rows 49 262 524 74 16 32 64 128 256 512), losses := [] }

theorem upper_76 : Upper D R [48,260,520,66] 13 :=
  bound_sound D R [48,260,520,66] 13 bound_76
    ((Boolean.boundCheck_true D R [48,260,520,66] 13 bound_76).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 262 524 88 243 227 227 227 483 739), lower := (rows 49 262 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_77 : Upper D R [48,260,520,80] 13 :=
  bound_sound D R [48,260,520,80] 13 bound_77
    ((Boolean.boundCheck_true D R [48,260,520,80] 13 bound_77).mp (by decide +kernel))

def bound_78 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 262 524 200 243 243 243 243 499 755), lower := (rows 49 262 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_78 : Upper D R [48,260,520,192] 13 :=
  bound_sound D R [48,260,520,192] 13 bound_78
    ((Boolean.boundCheck_true D R [48,260,520,192] 13 bound_78).mp (by decide +kernel))

def route_62 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_62 : Upper D R [48,260,520] 13 := by
  apply routed_branch D R [48,260,520] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] route_62
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260,520] (choices 2) [3,17,18,48,65,66,80,192] route_62).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_63
  · exact upper_72
  · exact upper_73
  · exact upper_74
  · exact upper_75
  · exact upper_76
  · exact upper_77
  · exact upper_78

def bound_79 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 262 532 235 251 235 235 235 491 747), lower := (rows 49 262 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_79 : Upper D R [48,260,528] 13 :=
  bound_sound D R [48,260,528] 13 bound_79
    ((Boolean.boundCheck_true D R [48,260,528] 13 bound_79).mp (by decide +kernel))

def bound_80 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 262 580 251 251 251 251 251 507 763), lower := (rows 49 262 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_80 : Upper D R [48,260,576] 13 :=
  bound_sound D R [48,260,576] 13 bound_80
    ((Boolean.boundCheck_true D R [48,260,576] 13 bound_80).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [48,260] 13 := by
  apply routed_branch D R [48,260] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192,513,514,520,528,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,260] (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192,513,514,520,528,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_7
  · exact upper_24
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_56
  · exact upper_62
  · exact upper_79
  · exact upper_80

theorem upper : Upper D R [48,260] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case31
