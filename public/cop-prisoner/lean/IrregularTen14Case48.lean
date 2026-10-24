import IrregularTen14Base

namespace Delivery.IrregularTen14.Case48
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 7 56 728 744 712 712 968 712), lower := (rows 273 38 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,36,3,48] 13 :=
  bound_sound D R [272,36,3,48] 13 bound_2
    ((Boolean.boundCheck_true D R [272,36,3,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 7 88 760 744 744 744 1000 744), lower := (rows 273 38 7 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,36,3,80] 13 :=
  bound_sound D R [272,36,3,80] 13 bound_3
    ((Boolean.boundCheck_true D R [272,36,3,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 7 104 728 760 728 728 984 728), lower := (rows 273 38 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [272,36,3,96] 13 :=
  bound_sound D R [272,36,3,96] 13 bound_4
    ((Boolean.boundCheck_true D R [272,36,3,96] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 7 200 760 760 760 760 1016 760), lower := (rows 273 38 7 200 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [272,36,3,192] 13 :=
  bound_sound D R [272,36,3,192] 13 bound_5
    ((Boolean.boundCheck_true D R [272,36,3,192] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 7 536 248 232 232 232 488 744), lower := (rows 273 38 7 536 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [272,36,3,528] 13 :=
  bound_sound D R [272,36,3,528] 13 bound_6
    ((Boolean.boundCheck_true D R [272,36,3,528] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 7 552 216 248 216 216 472 728), lower := (rows 273 38 7 552 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [272,36,3,544] 13 :=
  bound_sound D R [272,36,3,544] 13 bound_7
    ((Boolean.boundCheck_true D R [272,36,3,544] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 7 584 248 248 248 248 504 760), lower := (rows 273 38 7 584 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [272,36,3,576] 13 :=
  bound_sound D R [272,36,3,576] 13 bound_8
    ((Boolean.boundCheck_true D R [272,36,3,576] 13 bound_8).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,36,3] 13 := by
  apply routed_branch D R [272,36,3] 13 (by decide) (choices 2) [48,80,96,192,528,544,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,3] (choices 2) [48,80,96,192,528,544,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8

def bound_10 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 13 26 752 736 736 736 992 736), lower := (rows 273 38 13 26 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [272,36,9,18] 13 :=
  bound_sound D R [272,36,9,18] 13 bound_10
    ((Boolean.boundCheck_true D R [272,36,9,18] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 13 42 720 752 720 720 976 720), lower := (rows 273 38 13 42 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [272,36,9,34] 13 :=
  bound_sound D R [272,36,9,34] 13 bound_11
    ((Boolean.boundCheck_true D R [272,36,9,34] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 13 56 722 738 706 706 962 706), lower := (rows 273 38 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [272,36,9,48] 13 :=
  bound_sound D R [272,36,9,48] 13 bound_12
    ((Boolean.boundCheck_true D R [272,36,9,48] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 13 74 752 752 752 752 1008 752), lower := (rows 273 38 13 74 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [272,36,9,66] 13 :=
  bound_sound D R [272,36,9,66] 13 bound_13
    ((Boolean.boundCheck_true D R [272,36,9,66] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 13 88 754 738 738 738 994 738), lower := (rows 273 38 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_14 : Upper D R [272,36,9,80] 13 :=
  bound_sound D R [272,36,9,80] 13 bound_14
    ((Boolean.boundCheck_true D R [272,36,9,80] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 13 104 722 754 722 722 978 722), lower := (rows 273 38 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [272,36,9,96] 13 :=
  bound_sound D R [272,36,9,96] 13 bound_15
    ((Boolean.boundCheck_true D R [272,36,9,96] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 13 200 754 754 754 754 1010 754), lower := (rows 273 38 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [272,36,9,192] 13 :=
  bound_sound D R [272,36,9,192] 13 bound_16
    ((Boolean.boundCheck_true D R [272,36,9,192] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 48 240 208 208 464 720), lower := (rows 273 38 13 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 6 973 522 977 0 64 128 256 512) }] }

theorem upper_18 : Upper D R [272,36,9,514,32] 13 :=
  bound_sound D R [272,36,9,514,32] 13 bound_18
    ((Boolean.boundCheck_true D R [272,36,9,514,32] 13 bound_18).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 48 224 224 480 736), lower := (rows 273 38 13 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 32 98 162 290 546), good := (rows 257 1006 13 970 64 992 64 128 256 512) }] }

theorem upper_20 : Upper D R [272,36,9,514,64,16] 13 :=
  bound_sound D R [272,36,9,514,64,16] 13 bound_20
    ((Boolean.boundCheck_true D R [272,36,9,514,64,16] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 96 80 160 416 672), lower := (rows 273 38 13 522 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 15 0 112 64 243 371 627), good := (rows 943 942 911 906 992 992 992 128 256 512) }] }

theorem upper_22 : Upper D R [272,36,9,514,64,64,16] 13 :=
  bound_sound D R [272,36,9,514,64,64,16] 13 bound_22
    ((Boolean.boundCheck_true D R [272,36,9,514,64,64,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 96 96 144 400 656), lower := (rows 273 38 13 522 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 128 256 512), good := (rows 353 102 111 618 96 96 96 224 352 608) }] }

theorem upper_23 : Upper D R [272,36,9,514,64,64,32] 13 :=
  bound_sound D R [272,36,9,514,64,64,32] 13 bound_23
    ((Boolean.boundCheck_true D R [272,36,9,514,64,64,32] 13 bound_23).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 96 192 144 416 672), lower := (rows 273 38 13 522 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 214 221 730 208 208 208 208 465 720) }] }

theorem upper_25 : Upper D R [272,36,9,514,64,64,128,16] 13 :=
  bound_sound D R [272,36,9,514,64,64,128,16] 13 bound_25
    ((Boolean.boundCheck_true D R [272,36,9,514,64,64,128,16] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 96 192 160 400 656), lower := (rows 273 38 13 522 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 239 746 224 224 224 224 480 736) }] }

theorem upper_26 : Upper D R [272,36,9,514,64,64,128,32] 13 :=
  bound_sound D R [272,36,9,514,64,64,128,32] 13 bound_26
    ((Boolean.boundCheck_true D R [272,36,9,514,64,64,128,32] 13 bound_26).mp (by decide +kernel))

def route_24 : Route 10 := (fun mask => (mask,id))

theorem upper_24 : Upper D R [272,36,9,514,64,64,128] 13 := by
  apply routed_branch D R [272,36,9,514,64,64,128] 13 (by decide) (choices 1) [16,32] route_24
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514,64,64,128] (choices 1) [16,32] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_25
  · exact upper_26

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [272,36,9,514,64,64] 13 := by
  apply routed_branch D R [272,36,9,514,64,64] 13 (by decide) (choices 1) [16,32,128] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514,64,64] (choices 1) [16,32,128] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_22
  · exact upper_23
  · exact upper_24

def bound_28 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 160 80 224 480 736), lower := (rows 273 38 13 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 9 0 241 64 208 336 592), good := (rows 943 38 47 522 992 160 992 160 256 512) }] }

theorem upper_28 : Upper D R [272,36,9,514,64,128,16] 13 :=
  bound_sound D R [272,36,9,514,64,128,16] 13 bound_28
    ((Boolean.boundCheck_true D R [272,36,9,514,64,128,16] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 160 96 208 464 720), lower := (rows 273 38 13 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 6 13 522 977 128 977 128 256 512) }] }

theorem upper_29 : Upper D R [272,36,9,514,64,128,32] 13 :=
  bound_sound D R [272,36,9,514,64,128,32] 13 bound_29
    ((Boolean.boundCheck_true D R [272,36,9,514,64,128,32] 13 bound_29).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 160 192 144 352 608), lower := (rows 273 38 13 522 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 224 224 128 498 754), good := (rows 769 878 13 778 864 992 992 992 256 512) }] }

theorem upper_31 : Upper D R [272,36,9,514,64,128,128,16] 13 :=
  bound_sound D R [272,36,9,514,64,128,128,16] 13 bound_31
    ((Boolean.boundCheck_true D R [272,36,9,514,64,128,128,16] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 160 192 160 336 592), lower := (rows 273 38 13 522 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 239 746 224 224 224 224 480 736) }] }

theorem upper_32 : Upper D R [272,36,9,514,64,128,128,32] 13 :=
  bound_sound D R [272,36,9,514,64,128,128,32] 13 bound_32
    ((Boolean.boundCheck_true D R [272,36,9,514,64,128,128,32] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 13 522 80 160 192 192 304 560), lower := (rows 273 38 13 522 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 239 746 224 224 224 224 480 736) }] }

theorem upper_33 : Upper D R [272,36,9,514,64,128,128,64] 13 :=
  bound_sound D R [272,36,9,514,64,128,128,64] 13 bound_33
    ((Boolean.boundCheck_true D R [272,36,9,514,64,128,128,64] 13 bound_33).mp (by decide +kernel))

def route_30 : Route 10 := (fun mask => (mask,id))

theorem upper_30 : Upper D R [272,36,9,514,64,128,128] 13 := by
  apply routed_branch D R [272,36,9,514,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514,64,128,128] (choices 1) [16,32,64] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_31
  · exact upper_32
  · exact upper_33

def route_27 : Route 10 := (fun mask => (mask,id))

theorem upper_27 : Upper D R [272,36,9,514,64,128] 13 := by
  apply routed_branch D R [272,36,9,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_27
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514,64,128] (choices 1) [16,32,128] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30

def route_19 : Route 10 := (fun mask => (mask,id))

theorem upper_19 : Upper D R [272,36,9,514,64] 13 := by
  apply routed_branch D R [272,36,9,514,64] 13 (by decide) (choices 1) [16,64,128] route_19
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514,64] (choices 1) [16,64,128] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_20
  · exact upper_21
  · exact upper_27

def route_17 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_17 : Upper D R [272,36,9,514] 13 := by
  apply routed_branch D R [272,36,9,514] 13 (by decide) (choices 1) [32,64] route_17
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,9,514] (choices 1) [32,64] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_18
  · exact upper_19

def bound_34 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 13 536 242 226 226 226 482 738), lower := (rows 273 38 13 536 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [272,36,9,528] 13 :=
  bound_sound D R [272,36,9,528] 13 bound_34
    ((Boolean.boundCheck_true D R [272,36,9,528] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 13 552 210 242 210 210 466 722), lower := (rows 273 38 13 552 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [272,36,9,544] 13 :=
  bound_sound D R [272,36,9,544] 13 bound_35
    ((Boolean.boundCheck_true D R [272,36,9,544] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 13 584 242 242 242 242 498 754), lower := (rows 273 38 13 584 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,36,9,576] 13 :=
  bound_sound D R [272,36,9,576] 13 bound_36
    ((Boolean.boundCheck_true D R [272,36,9,576] 13 bound_36).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [272,36,9] 13 := by
  apply routed_branch D R [272,36,9] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_9
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,9] (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13
  · exact upper_14
  · exact upper_15
  · exact upper_16
  · exact upper_17
  · exact upper_34
  · exact upper_35
  · exact upper_36

def bound_38 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 14 25 752 736 736 736 992 736), lower := (rows 273 38 14 25 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [272,36,10,17] 13 :=
  bound_sound D R [272,36,10,17] 13 bound_38
    ((Boolean.boundCheck_true D R [272,36,10,17] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 14 41 720 752 720 720 976 720), lower := (rows 273 38 14 41 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [272,36,10,33] 13 :=
  bound_sound D R [272,36,10,33] 13 bound_39
    ((Boolean.boundCheck_true D R [272,36,10,33] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 14 56 721 737 705 705 961 705), lower := (rows 273 38 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [272,36,10,48] 13 :=
  bound_sound D R [272,36,10,48] 13 bound_40
    ((Boolean.boundCheck_true D R [272,36,10,48] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 14 73 752 752 752 752 1008 752), lower := (rows 273 38 14 73 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [272,36,10,65] 13 :=
  bound_sound D R [272,36,10,65] 13 bound_41
    ((Boolean.boundCheck_true D R [272,36,10,65] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 14 88 753 737 737 737 993 737), lower := (rows 273 38 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [272,36,10,80] 13 :=
  bound_sound D R [272,36,10,80] 13 bound_42
    ((Boolean.boundCheck_true D R [272,36,10,80] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 14 104 721 753 721 721 977 721), lower := (rows 273 38 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [272,36,10,96] 13 :=
  bound_sound D R [272,36,10,96] 13 bound_43
    ((Boolean.boundCheck_true D R [272,36,10,96] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 14 200 753 753 753 753 1009 753), lower := (rows 273 38 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [272,36,10,192] 13 :=
  bound_sound D R [272,36,10,192] 13 bound_44
    ((Boolean.boundCheck_true D R [272,36,10,192] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 14 521 48 240 208 208 464 720), lower := (rows 273 38 14 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 25 16 0 81 145 273 529), good := (rows 985 6 14 969 985 0 64 128 256 512) }] }

theorem upper_46 : Upper D R [272,36,10,513,32] 13 :=
  bound_sound D R [272,36,10,513,32] 13 bound_46
    ((Boolean.boundCheck_true D R [272,36,10,513,32] 13 bound_46).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 224 144 176 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 48 224 224 480 736), lower := (rows 273 38 14 521 80 48 64 128 256 512), losses := [{ target := 6, region := (rows 1 10 12 8 16 49 0 128 256 512), good := (rows 305 38 14 559 48 48 0 128 256 512) }] }

theorem upper_48 : Upper D R [272,36,10,513,64,16] 13 :=
  bound_sound D R [272,36,10,513,64,16] 13 bound_48
    ((Boolean.boundCheck_true D R [272,36,10,513,64,16] 13 bound_48).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 96 80 160 416 672), lower := (rows 273 38 14 521 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 13 9 0 112 64 243 371 627), good := (rows 943 934 910 911 992 992 992 128 256 512) }] }

theorem upper_50 : Upper D R [272,36,10,513,64,64,16] 13 :=
  bound_sound D R [272,36,10,513,64,64,16] 13 bound_50
    ((Boolean.boundCheck_true D R [272,36,10,513,64,64,16] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 192 224 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 96 96 144 400 656), lower := (rows 273 38 14 521 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 1023 1023 128 256 512), good := (rows 353 102 110 623 96 96 96 224 352 608) }] }

theorem upper_51 : Upper D R [272,36,10,513,64,64,32] 13 :=
  bound_sound D R [272,36,10,513,64,64,32] 13 bound_51
    ((Boolean.boundCheck_true D R [272,36,10,513,64,64,32] 13 bound_51).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 96 192 144 416 672), lower := (rows 273 38 14 521 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 214 222 729 208 208 208 208 465 720) }] }

theorem upper_53 : Upper D R [272,36,10,513,64,64,128,16] 13 :=
  bound_sound D R [272,36,10,513,64,64,128,16] 13 bound_53
    ((Boolean.boundCheck_true D R [272,36,10,513,64,64,128,16] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 192 224 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 96 192 160 400 656), lower := (rows 273 38 14 521 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 1023 1023 1023 256 512), good := (rows 481 230 238 751 224 224 224 224 480 736) }] }

theorem upper_54 : Upper D R [272,36,10,513,64,64,128,32] 13 :=
  bound_sound D R [272,36,10,513,64,64,128,32] 13 bound_54
    ((Boolean.boundCheck_true D R [272,36,10,513,64,64,128,32] 13 bound_54).mp (by decide +kernel))

def route_52 : Route 10 := (fun mask => (mask,id))

theorem upper_52 : Upper D R [272,36,10,513,64,64,128] 13 := by
  apply routed_branch D R [272,36,10,513,64,64,128] 13 (by decide) (choices 1) [16,32] route_52
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513,64,64,128] (choices 1) [16,32] route_52).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_53
  · exact upper_54

def route_49 : Route 10 := (fun mask => (mask,id))

theorem upper_49 : Upper D R [272,36,10,513,64,64] 13 := by
  apply routed_branch D R [272,36,10,513,64,64] 13 (by decide) (choices 1) [16,32,128] route_49
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513,64,64] (choices 1) [16,32,128] route_49).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_50
  · exact upper_51
  · exact upper_52

def bound_56 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 160 80 224 480 736), lower := (rows 273 38 14 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 13 9 0 241 64 208 336 592), good := (rows 943 38 14 559 992 160 992 160 256 512) }] }

theorem upper_56 : Upper D R [272,36,10,513,64,128,16] 13 :=
  bound_sound D R [272,36,10,513,64,128,16] 13 bound_56
    ((Boolean.boundCheck_true D R [272,36,10,513,64,128,16] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 160 96 208 464 720), lower := (rows 273 38 14 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 89 80 0 64 208 336 592), good := (rows 921 6 14 521 985 128 985 128 256 512) }] }

theorem upper_57 : Upper D R [272,36,10,513,64,128,32] 13 :=
  bound_sound D R [272,36,10,513,64,128,32] 13 bound_57
    ((Boolean.boundCheck_true D R [272,36,10,513,64,128,32] 13 bound_57).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 160 192 144 352 608), lower := (rows 273 38 14 521 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 224 224 128 498 754), good := (rows 777 870 782 521 864 992 992 992 256 512) }] }

theorem upper_59 : Upper D R [272,36,10,513,64,128,128,16] 13 :=
  bound_sound D R [272,36,10,513,64,128,128,16] 13 bound_59
    ((Boolean.boundCheck_true D R [272,36,10,513,64,128,128,16] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 192 224 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 160 192 160 336 592), lower := (rows 273 38 14 521 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 1023 1023 1023 256 512), good := (rows 481 230 238 751 224 224 224 224 480 736) }] }

theorem upper_60 : Upper D R [272,36,10,513,64,128,128,32] 13 :=
  bound_sound D R [272,36,10,513,64,128,128,32] 13 bound_60
    ((Boolean.boundCheck_true D R [272,36,10,513,64,128,128,32] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 192 224 240 0 0 0 0 0 0), upper := (rows 273 38 14 521 80 160 192 192 304 560), lower := (rows 273 38 14 521 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 1023 1023 1023 256 512), good := (rows 481 230 238 751 224 224 224 224 480 736) }] }

theorem upper_61 : Upper D R [272,36,10,513,64,128,128,64] 13 :=
  bound_sound D R [272,36,10,513,64,128,128,64] 13 bound_61
    ((Boolean.boundCheck_true D R [272,36,10,513,64,128,128,64] 13 bound_61).mp (by decide +kernel))

def route_58 : Route 10 := (fun mask => (mask,id))

theorem upper_58 : Upper D R [272,36,10,513,64,128,128] 13 := by
  apply routed_branch D R [272,36,10,513,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_58
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513,64,128,128] (choices 1) [16,32,64] route_58).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_59
  · exact upper_60
  · exact upper_61

def route_55 : Route 10 := (fun mask => (mask,id))

theorem upper_55 : Upper D R [272,36,10,513,64,128] 13 := by
  apply routed_branch D R [272,36,10,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_55
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513,64,128] (choices 1) [16,32,128] route_55).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_56
  · exact upper_57
  · exact upper_58

def route_47 : Route 10 := (fun mask => (mask,id))

theorem upper_47 : Upper D R [272,36,10,513,64] 13 := by
  apply routed_branch D R [272,36,10,513,64] 13 (by decide) (choices 1) [16,64,128] route_47
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513,64] (choices 1) [16,64,128] route_47).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_48
  · exact upper_49
  · exact upper_55

def route_45 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_45 : Upper D R [272,36,10,513] 13 := by
  apply routed_branch D R [272,36,10,513] 13 (by decide) (choices 1) [32,64] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,10,513] (choices 1) [32,64] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_46
  · exact upper_47

def bound_62 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 14 536 241 225 225 225 481 737), lower := (rows 273 38 14 536 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [272,36,10,528] 13 :=
  bound_sound D R [272,36,10,528] 13 bound_62
    ((Boolean.boundCheck_true D R [272,36,10,528] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 14 552 209 241 209 209 465 721), lower := (rows 273 38 14 552 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [272,36,10,544] 13 :=
  bound_sound D R [272,36,10,544] 13 bound_63
    ((Boolean.boundCheck_true D R [272,36,10,544] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 14 584 241 241 241 241 497 753), lower := (rows 273 38 14 584 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [272,36,10,576] 13 :=
  bound_sound D R [272,36,10,576] 13 bound_64
    ((Boolean.boundCheck_true D R [272,36,10,576] 13 bound_64).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_37 : Upper D R [272,36,10] 13 := by
  apply routed_branch D R [272,36,10] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_37
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,10] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_62
  · exact upper_63
  · exact upper_64

def bound_65 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 21 746 762 746 746 746 1002 746), lower := (rows 273 38 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [272,36,17] 13 :=
  bound_sound D R [272,36,17] 13 bound_65
    ((Boolean.boundCheck_true D R [272,36,17] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 22 745 761 745 745 745 1001 745), lower := (rows 273 38 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [272,36,18] 13 :=
  bound_sound D R [272,36,18] 13 bound_66
    ((Boolean.boundCheck_true D R [272,36,18] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 28 747 755 739 739 739 995 739), lower := (rows 273 38 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [272,36,24] 13 :=
  bound_sound D R [272,36,24] 13 bound_67
    ((Boolean.boundCheck_true D R [272,36,24] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 38 37 730 730 762 730 730 986 730), lower := (rows 273 38 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_68 : Upper D R [272,36,33] 13 :=
  bound_sound D R [272,36,33] 13 bound_68
    ((Boolean.boundCheck_true D R [272,36,33] 13 bound_68).mp (by decide +kernel))

def bound_69 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 38 38 729 729 761 729 729 985 729), lower := (rows 273 38 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_69 : Upper D R [272,36,34] 13 :=
  bound_sound D R [272,36,34] 13 bound_69
    ((Boolean.boundCheck_true D R [272,36,34] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 38 44 731 723 755 723 723 979 723), lower := (rows 273 38 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [272,36,40] 13 :=
  bound_sound D R [272,36,40] 13 bound_70
    ((Boolean.boundCheck_true D R [272,36,40] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 273 38 52 715 731 747 715 715 971 715), lower := (rows 273 38 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [272,36,48] 13 :=
  bound_sound D R [272,36,48] 13 bound_71
    ((Boolean.boundCheck_true D R [272,36,48] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 38 69 762 762 762 762 762 1018 762), lower := (rows 273 38 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [272,36,65] 13 :=
  bound_sound D R [272,36,65] 13 bound_72
    ((Boolean.boundCheck_true D R [272,36,65] 13 bound_72).mp (by decide +kernel))

def bound_73 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 38 70 761 761 761 761 761 1017 761), lower := (rows 273 38 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_73 : Upper D R [272,36,66] 13 :=
  bound_sound D R [272,36,66] 13 bound_73
    ((Boolean.boundCheck_true D R [272,36,66] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 38 76 763 755 755 755 755 1011 755), lower := (rows 273 38 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_74 : Upper D R [272,36,72] 13 :=
  bound_sound D R [272,36,72] 13 bound_74
    ((Boolean.boundCheck_true D R [272,36,72] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 273 38 84 747 763 747 747 747 1003 747), lower := (rows 273 38 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_75 : Upper D R [272,36,80] 13 :=
  bound_sound D R [272,36,80] 13 bound_75
    ((Boolean.boundCheck_true D R [272,36,80] 13 bound_75).mp (by decide +kernel))

def bound_76 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 273 38 100 731 731 763 731 731 987 731), lower := (rows 273 38 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_76 : Upper D R [272,36,96] 13 :=
  bound_sound D R [272,36,96] 13 bound_76
    ((Boolean.boundCheck_true D R [272,36,96] 13 bound_76).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 273 38 196 763 763 763 763 763 1019 763), lower := (rows 273 38 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_77 : Upper D R [272,36,192] 13 :=
  bound_sound D R [272,36,192] 13 bound_77
    ((Boolean.boundCheck_true D R [272,36,192] 13 bound_77).mp (by decide +kernel))

def bound_79 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 517 26 248 232 232 232 488 744), lower := (rows 273 38 517 26 16 32 64 128 256 512), losses := [] }

theorem upper_79 : Upper D R [272,36,513,18] 13 :=
  bound_sound D R [272,36,513,18] 13 bound_79
    ((Boolean.boundCheck_true D R [272,36,513,18] 13 bound_79).mp (by decide +kernel))

def bound_80 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 517 42 216 248 216 216 472 728), lower := (rows 273 38 517 42 16 32 64 128 256 512), losses := [] }

theorem upper_80 : Upper D R [272,36,513,34] 13 :=
  bound_sound D R [272,36,513,34] 13 bound_80
    ((Boolean.boundCheck_true D R [272,36,513,34] 13 bound_80).mp (by decide +kernel))

def bound_81 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 517 56 218 234 202 202 458 714), lower := (rows 273 38 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_81 : Upper D R [272,36,513,48] 13 :=
  bound_sound D R [272,36,513,48] 13 bound_81
    ((Boolean.boundCheck_true D R [272,36,513,48] 13 bound_81).mp (by decide +kernel))

def bound_82 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 517 74 248 248 248 248 504 760), lower := (rows 273 38 517 74 16 32 64 128 256 512), losses := [] }

theorem upper_82 : Upper D R [272,36,513,66] 13 :=
  bound_sound D R [272,36,513,66] 13 bound_82
    ((Boolean.boundCheck_true D R [272,36,513,66] 13 bound_82).mp (by decide +kernel))

def bound_83 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 517 88 250 234 234 234 490 746), lower := (rows 273 38 517 88 16 32 64 128 256 512), losses := [] }

theorem upper_83 : Upper D R [272,36,513,80] 13 :=
  bound_sound D R [272,36,513,80] 13 bound_83
    ((Boolean.boundCheck_true D R [272,36,513,80] 13 bound_83).mp (by decide +kernel))

def bound_84 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 517 104 218 250 218 218 474 730), lower := (rows 273 38 517 104 16 32 64 128 256 512), losses := [] }

theorem upper_84 : Upper D R [272,36,513,96] 13 :=
  bound_sound D R [272,36,513,96] 13 bound_84
    ((Boolean.boundCheck_true D R [272,36,513,96] 13 bound_84).mp (by decide +kernel))

def bound_85 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 517 200 250 250 250 250 506 762), lower := (rows 273 38 517 200 16 32 64 128 256 512), losses := [] }

theorem upper_85 : Upper D R [272,36,513,192] 13 :=
  bound_sound D R [272,36,513,192] 13 bound_85
    ((Boolean.boundCheck_true D R [272,36,513,192] 13 bound_85).mp (by decide +kernel))

def route_78 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_78 : Upper D R [272,36,513] 13 := by
  apply routed_branch D R [272,36,513] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] route_78
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,513] (choices 2) [18,34,48,66,80,96,192] route_78).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_79
  · exact upper_80
  · exact upper_81
  · exact upper_82
  · exact upper_83
  · exact upper_84
  · exact upper_85

def bound_87 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 518 25 248 232 232 232 488 744), lower := (rows 273 38 518 25 16 32 64 128 256 512), losses := [] }

theorem upper_87 : Upper D R [272,36,514,17] 13 :=
  bound_sound D R [272,36,514,17] 13 bound_87
    ((Boolean.boundCheck_true D R [272,36,514,17] 13 bound_87).mp (by decide +kernel))

def bound_88 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 518 41 216 248 216 216 472 728), lower := (rows 273 38 518 41 16 32 64 128 256 512), losses := [] }

theorem upper_88 : Upper D R [272,36,514,33] 13 :=
  bound_sound D R [272,36,514,33] 13 bound_88
    ((Boolean.boundCheck_true D R [272,36,514,33] 13 bound_88).mp (by decide +kernel))

def bound_89 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 518 56 217 233 201 201 457 713), lower := (rows 273 38 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_89 : Upper D R [272,36,514,48] 13 :=
  bound_sound D R [272,36,514,48] 13 bound_89
    ((Boolean.boundCheck_true D R [272,36,514,48] 13 bound_89).mp (by decide +kernel))

def bound_90 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 518 73 248 248 248 248 504 760), lower := (rows 273 38 518 73 16 32 64 128 256 512), losses := [] }

theorem upper_90 : Upper D R [272,36,514,65] 13 :=
  bound_sound D R [272,36,514,65] 13 bound_90
    ((Boolean.boundCheck_true D R [272,36,514,65] 13 bound_90).mp (by decide +kernel))

def bound_91 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 518 88 249 233 233 233 489 745), lower := (rows 273 38 518 88 16 32 64 128 256 512), losses := [] }

theorem upper_91 : Upper D R [272,36,514,80] 13 :=
  bound_sound D R [272,36,514,80] 13 bound_91
    ((Boolean.boundCheck_true D R [272,36,514,80] 13 bound_91).mp (by decide +kernel))

def bound_92 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 518 104 217 249 217 217 473 729), lower := (rows 273 38 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_92 : Upper D R [272,36,514,96] 13 :=
  bound_sound D R [272,36,514,96] 13 bound_92
    ((Boolean.boundCheck_true D R [272,36,514,96] 13 bound_92).mp (by decide +kernel))

def bound_93 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 518 200 249 249 249 249 505 761), lower := (rows 273 38 518 200 16 32 64 128 256 512), losses := [] }

theorem upper_93 : Upper D R [272,36,514,192] 13 :=
  bound_sound D R [272,36,514,192] 13 bound_93
    ((Boolean.boundCheck_true D R [272,36,514,192] 13 bound_93).mp (by decide +kernel))

def route_86 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_86 : Upper D R [272,36,514] 13 := by
  apply routed_branch D R [272,36,514] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] route_86
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,514] (choices 2) [17,33,48,65,80,96,192] route_86).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_87
  · exact upper_88
  · exact upper_89
  · exact upper_90
  · exact upper_91
  · exact upper_92
  · exact upper_93

def bound_96 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 48 240 208 208 464 720), lower := (rows 273 38 524 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 12 8 16 0 81 145 273 529), good := (rows 977 6 524 975 977 0 64 128 256 512) }] }

theorem upper_96 : Upper D R [272,36,520,3,32] 13 :=
  bound_sound D R [272,36,520,3,32] 13 bound_96
    ((Boolean.boundCheck_true D R [272,36,520,3,32] 13 bound_96).mp (by decide +kernel))

def bound_98 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 48 224 224 480 736), lower := (rows 273 38 524 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 98 162 290 546), good := (rows 257 998 524 975 64 992 64 128 256 512) }] }

theorem upper_98 : Upper D R [272,36,520,3,64,16] 13 :=
  bound_sound D R [272,36,520,3,64,16] 13 bound_98
    ((Boolean.boundCheck_true D R [272,36,520,3,64,16] 13 bound_98).mp (by decide +kernel))

def bound_100 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 96 80 160 416 672), lower := (rows 273 38 524 11 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 13 9 0 112 64 243 371 627), good := (rows 943 934 524 911 992 992 992 128 256 512) }] }

theorem upper_100 : Upper D R [272,36,520,3,64,64,16] 13 :=
  bound_sound D R [272,36,520,3,64,64,16] 13 bound_100
    ((Boolean.boundCheck_true D R [272,36,520,3,64,64,16] 13 bound_100).mp (by decide +kernel))

def bound_101 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 96 96 144 400 656), lower := (rows 273 38 524 11 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 128 256 512), good := (rows 353 102 622 107 96 96 96 224 352 608) }] }

theorem upper_101 : Upper D R [272,36,520,3,64,64,32] 13 :=
  bound_sound D R [272,36,520,3,64,64,32] 13 bound_101
    ((Boolean.boundCheck_true D R [272,36,520,3,64,64,32] 13 bound_101).mp (by decide +kernel))

def bound_103 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 96 192 144 416 672), lower := (rows 273 38 524 11 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 214 732 219 208 208 208 208 465 720) }] }

theorem upper_103 : Upper D R [272,36,520,3,64,64,128,16] 13 :=
  bound_sound D R [272,36,520,3,64,64,128,16] 13 bound_103
    ((Boolean.boundCheck_true D R [272,36,520,3,64,64,128,16] 13 bound_103).mp (by decide +kernel))

def bound_104 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 96 192 160 400 656), lower := (rows 273 38 524 11 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 750 235 224 224 224 224 480 736) }] }

theorem upper_104 : Upper D R [272,36,520,3,64,64,128,32] 13 :=
  bound_sound D R [272,36,520,3,64,64,128,32] 13 bound_104
    ((Boolean.boundCheck_true D R [272,36,520,3,64,64,128,32] 13 bound_104).mp (by decide +kernel))

def route_102 : Route 10 := (fun mask => (mask,id))

theorem upper_102 : Upper D R [272,36,520,3,64,64,128] 13 := by
  apply routed_branch D R [272,36,520,3,64,64,128] 13 (by decide) (choices 1) [16,32] route_102
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3,64,64,128] (choices 1) [16,32] route_102).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_103
  · exact upper_104

def route_99 : Route 10 := (fun mask => (mask,id))

theorem upper_99 : Upper D R [272,36,520,3,64,64] 13 := by
  apply routed_branch D R [272,36,520,3,64,64] 13 (by decide) (choices 1) [16,32,128] route_99
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3,64,64] (choices 1) [16,32,128] route_99).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_100
  · exact upper_101
  · exact upper_102

def bound_106 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 160 80 224 480 736), lower := (rows 273 38 524 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 5 9 0 241 64 208 336 592), good := (rows 943 38 526 47 992 160 992 160 256 512) }] }

theorem upper_106 : Upper D R [272,36,520,3,64,128,16] 13 :=
  bound_sound D R [272,36,520,3,64,128,16] 13 bound_106
    ((Boolean.boundCheck_true D R [272,36,520,3,64,128,16] 13 bound_106).mp (by decide +kernel))

def bound_107 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 160 96 208 464 720), lower := (rows 273 38 524 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 6 524 11 977 128 977 128 256 512) }] }

theorem upper_107 : Upper D R [272,36,520,3,64,128,32] 13 :=
  bound_sound D R [272,36,520,3,64,128,32] 13 bound_107
    ((Boolean.boundCheck_true D R [272,36,520,3,64,128,32] 13 bound_107).mp (by decide +kernel))

def bound_109 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 160 192 144 352 608), lower := (rows 273 38 524 11 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 224 224 128 498 754), good := (rows 769 870 524 783 864 992 992 992 256 512) }] }

theorem upper_109 : Upper D R [272,36,520,3,64,128,128,16] 13 :=
  bound_sound D R [272,36,520,3,64,128,128,16] 13 bound_109
    ((Boolean.boundCheck_true D R [272,36,520,3,64,128,128,16] 13 bound_109).mp (by decide +kernel))

def bound_110 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 160 192 160 336 592), lower := (rows 273 38 524 11 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 750 235 224 224 224 224 480 736) }] }

theorem upper_110 : Upper D R [272,36,520,3,64,128,128,32] 13 :=
  bound_sound D R [272,36,520,3,64,128,128,32] 13 bound_110
    ((Boolean.boundCheck_true D R [272,36,520,3,64,128,128,32] 13 bound_110).mp (by decide +kernel))

def bound_111 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 38 524 11 80 160 192 192 304 560), lower := (rows 273 38 524 11 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 256 512), good := (rows 481 230 750 235 224 224 224 224 480 736) }] }

theorem upper_111 : Upper D R [272,36,520,3,64,128,128,64] 13 :=
  bound_sound D R [272,36,520,3,64,128,128,64] 13 bound_111
    ((Boolean.boundCheck_true D R [272,36,520,3,64,128,128,64] 13 bound_111).mp (by decide +kernel))

def route_108 : Route 10 := (fun mask => (mask,id))

theorem upper_108 : Upper D R [272,36,520,3,64,128,128] 13 := by
  apply routed_branch D R [272,36,520,3,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_108
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3,64,128,128] (choices 1) [16,32,64] route_108).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_109
  · exact upper_110
  · exact upper_111

def route_105 : Route 10 := (fun mask => (mask,id))

theorem upper_105 : Upper D R [272,36,520,3,64,128] 13 := by
  apply routed_branch D R [272,36,520,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_105
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3,64,128] (choices 1) [16,32,128] route_105).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_106
  · exact upper_107
  · exact upper_108

def route_97 : Route 10 := (fun mask => (mask,id))

theorem upper_97 : Upper D R [272,36,520,3,64] 13 := by
  apply routed_branch D R [272,36,520,3,64] 13 (by decide) (choices 1) [16,64,128] route_97
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3,64] (choices 1) [16,64,128] route_97).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_98
  · exact upper_99
  · exact upper_105

def route_95 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_95 : Upper D R [272,36,520,3] 13 := by
  apply routed_branch D R [272,36,520,3] 13 (by decide) (choices 1) [32,64] route_95
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,36,520,3] (choices 1) [32,64] route_95).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_96
  · exact upper_97

def bound_112 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 524 25 242 226 226 226 482 738), lower := (rows 273 38 524 25 16 32 64 128 256 512), losses := [] }

theorem upper_112 : Upper D R [272,36,520,17] 13 :=
  bound_sound D R [272,36,520,17] 13 bound_112
    ((Boolean.boundCheck_true D R [272,36,520,17] 13 bound_112).mp (by decide +kernel))

def bound_113 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 38 524 26 241 225 225 225 481 737), lower := (rows 273 38 524 26 16 32 64 128 256 512), losses := [] }

theorem upper_113 : Upper D R [272,36,520,18] 13 :=
  bound_sound D R [272,36,520,18] 13 bound_113
    ((Boolean.boundCheck_true D R [272,36,520,18] 13 bound_113).mp (by decide +kernel))

def bound_114 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 524 41 210 242 210 210 466 722), lower := (rows 273 38 524 41 16 32 64 128 256 512), losses := [] }

theorem upper_114 : Upper D R [272,36,520,33] 13 :=
  bound_sound D R [272,36,520,33] 13 bound_114
    ((Boolean.boundCheck_true D R [272,36,520,33] 13 bound_114).mp (by decide +kernel))

def bound_115 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 38 524 42 209 241 209 209 465 721), lower := (rows 273 38 524 42 16 32 64 128 256 512), losses := [] }

theorem upper_115 : Upper D R [272,36,520,34] 13 :=
  bound_sound D R [272,36,520,34] 13 bound_115
    ((Boolean.boundCheck_true D R [272,36,520,34] 13 bound_115).mp (by decide +kernel))

def bound_116 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 38 524 56 211 227 195 195 451 707), lower := (rows 273 38 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_116 : Upper D R [272,36,520,48] 13 :=
  bound_sound D R [272,36,520,48] 13 bound_116
    ((Boolean.boundCheck_true D R [272,36,520,48] 13 bound_116).mp (by decide +kernel))

def bound_117 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 524 73 242 242 242 242 498 754), lower := (rows 273 38 524 73 16 32 64 128 256 512), losses := [] }

theorem upper_117 : Upper D R [272,36,520,65] 13 :=
  bound_sound D R [272,36,520,65] 13 bound_117
    ((Boolean.boundCheck_true D R [272,36,520,65] 13 bound_117).mp (by decide +kernel))

def bound_118 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 38 524 74 241 241 241 241 497 753), lower := (rows 273 38 524 74 16 32 64 128 256 512), losses := [] }

theorem upper_118 : Upper D R [272,36,520,66] 13 :=
  bound_sound D R [272,36,520,66] 13 bound_118
    ((Boolean.boundCheck_true D R [272,36,520,66] 13 bound_118).mp (by decide +kernel))

def bound_119 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 38 524 88 243 227 227 227 483 739), lower := (rows 273 38 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_119 : Upper D R [272,36,520,80] 13 :=
  bound_sound D R [272,36,520,80] 13 bound_119
    ((Boolean.boundCheck_true D R [272,36,520,80] 13 bound_119).mp (by decide +kernel))

def bound_120 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 38 524 104 211 243 211 211 467 723), lower := (rows 273 38 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_120 : Upper D R [272,36,520,96] 13 :=
  bound_sound D R [272,36,520,96] 13 bound_120
    ((Boolean.boundCheck_true D R [272,36,520,96] 13 bound_120).mp (by decide +kernel))

def bound_121 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 38 524 200 243 243 243 243 499 755), lower := (rows 273 38 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_121 : Upper D R [272,36,520,192] 13 :=
  bound_sound D R [272,36,520,192] 13 bound_121
    ((Boolean.boundCheck_true D R [272,36,520,192] 13 bound_121).mp (by decide +kernel))

def route_94 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_94 : Upper D R [272,36,520] 13 := by
  apply routed_branch D R [272,36,520] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_94
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36,520] (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_94).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_95
  · exact upper_112
  · exact upper_113
  · exact upper_114
  · exact upper_115
  · exact upper_116
  · exact upper_117
  · exact upper_118
  · exact upper_119
  · exact upper_120
  · exact upper_121

def bound_122 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 38 532 235 251 235 235 235 491 747), lower := (rows 273 38 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_122 : Upper D R [272,36,528] 13 :=
  bound_sound D R [272,36,528] 13 bound_122
    ((Boolean.boundCheck_true D R [272,36,528] 13 bound_122).mp (by decide +kernel))

def bound_123 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 38 548 219 219 251 219 219 475 731), lower := (rows 273 38 548 8 16 32 64 128 256 512), losses := [] }

theorem upper_123 : Upper D R [272,36,544] 13 :=
  bound_sound D R [272,36,544] 13 bound_123
    ((Boolean.boundCheck_true D R [272,36,544] 13 bound_123).mp (by decide +kernel))

def bound_124 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 38 580 251 251 251 251 251 507 763), lower := (rows 273 38 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_124 : Upper D R [272,36,576] 13 :=
  bound_sound D R [272,36,576] 13 bound_124
    ((Boolean.boundCheck_true D R [272,36,576] 13 bound_124).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,36] 13 := by
  apply routed_branch D R [272,36] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192,513,514,520,528,544,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,36] (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192,513,514,520,528,544,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_9
  · exact upper_37
  · exact upper_65
  · exact upper_66
  · exact upper_67
  · exact upper_68
  · exact upper_69
  · exact upper_70
  · exact upper_71
  · exact upper_72
  · exact upper_73
  · exact upper_74
  · exact upper_75
  · exact upper_76
  · exact upper_77
  · exact upper_78
  · exact upper_86
  · exact upper_94
  · exact upper_122
  · exact upper_123
  · exact upper_124

theorem upper : Upper D R [272,36] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case48
