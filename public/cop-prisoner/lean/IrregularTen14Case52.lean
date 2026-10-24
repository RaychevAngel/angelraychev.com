import IrregularTen14Base

namespace Delivery.IrregularTen14.Case52
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 7 56 248 232 232 232 488 744), lower := (rows 273 518 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,516,3,48] 13 :=
  bound_sound D R [272,516,3,48] 13 bound_2
    ((Boolean.boundCheck_true D R [272,516,3,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 518 7 104 248 248 248 248 504 760), lower := (rows 273 518 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,516,3,96] 13 :=
  bound_sound D R [272,516,3,96] 13 bound_3
    ((Boolean.boundCheck_true D R [272,516,3,96] 13 bound_3).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,516,3] 13 := by
  apply routed_branch D R [272,516,3] 13 (by decide) (choices 2) [48,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,3] (choices 2) [48,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_2
  · exact upper_3

def bound_5 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 273 518 13 26 240 224 224 224 480 736), lower := (rows 273 518 13 26 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 998 1007 1002 992 992 992 992 992 992) }] }

theorem upper_5 : Upper D R [272,516,9,18] 13 :=
  bound_sound D R [272,516,9,18] 13 bound_5
    ((Boolean.boundCheck_true D R [272,516,9,18] 13 bound_5).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 273 518 13 42 48 240 208 208 464 720), lower := (rows 273 518 13 42 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 6 4 8 16 0 81 145 273 529), good := (rows 977 518 975 10 977 0 64 128 256 512) }] }

theorem upper_7 : Upper D R [272,516,9,34,32] 13 :=
  bound_sound D R [272,516,9,34,32] 13 bound_7
    ((Boolean.boundCheck_true D R [272,516,9,34,32] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 48 224 224 480 736), lower := (rows 273 518 13 42 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 104 168 296 552), good := (rows 257 518 975 1002 64 992 64 128 256 512) }] }

theorem upper_9 : Upper D R [272,516,9,34,64,16] 13 :=
  bound_sound D R [272,516,9,34,64,16] 13 bound_9
    ((Boolean.boundCheck_true D R [272,516,9,34,64,16] 13 bound_9).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 96 80 160 416 672), lower := (rows 273 518 13 42 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 9 0 112 64 249 377 633), good := (rows 943 518 911 938 992 992 992 128 256 512) }] }

theorem upper_11 : Upper D R [272,516,9,34,64,64,16] 13 :=
  bound_sound D R [272,516,9,34,64,64,16] 13 bound_11
    ((Boolean.boundCheck_true D R [272,516,9,34,64,64,16] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 96 96 144 400 656), lower := (rows 273 518 13 42 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 128 256 512), good := (rows 353 622 109 106 96 96 96 224 352 608) }] }

theorem upper_12 : Upper D R [272,516,9,34,64,64,32] 13 :=
  bound_sound D R [272,516,9,34,64,64,32] 13 bound_12
    ((Boolean.boundCheck_true D R [272,516,9,34,64,64,32] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 96 192 144 416 672), lower := (rows 273 518 13 42 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 726 221 218 208 208 208 208 465 720) }] }

theorem upper_14 : Upper D R [272,516,9,34,64,64,128,16] 13 :=
  bound_sound D R [272,516,9,34,64,64,128,16] 13 bound_14
    ((Boolean.boundCheck_true D R [272,516,9,34,64,64,128,16] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 96 192 160 400 656), lower := (rows 273 518 13 42 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 750 237 234 224 224 224 224 480 736) }] }

theorem upper_15 : Upper D R [272,516,9,34,64,64,128,32] 13 :=
  bound_sound D R [272,516,9,34,64,64,128,32] 13 bound_15
    ((Boolean.boundCheck_true D R [272,516,9,34,64,64,128,32] 13 bound_15).mp (by decide +kernel))

def route_13 : Route 10 := (fun mask => (mask,id))

theorem upper_13 : Upper D R [272,516,9,34,64,64,128] 13 := by
  apply routed_branch D R [272,516,9,34,64,64,128] 13 (by decide) (choices 1) [16,32] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34,64,64,128] (choices 1) [16,32] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def route_10 : Route 10 := (fun mask => (mask,id))

theorem upper_10 : Upper D R [272,516,9,34,64,64] 13 := by
  apply routed_branch D R [272,516,9,34,64,64] 13 (by decide) (choices 1) [16,32,128] route_10
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34,64,64] (choices 1) [16,32,128] route_10).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_11
  · exact upper_12
  · exact upper_13

def bound_17 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 160 80 224 480 736), lower := (rows 273 518 13 42 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 13 0 241 64 208 336 592), good := (rows 943 526 47 42 992 160 992 160 256 512) }] }

theorem upper_17 : Upper D R [272,516,9,34,64,128,16] 13 :=
  bound_sound D R [272,516,9,34,64,128,16] 13 bound_17
    ((Boolean.boundCheck_true D R [272,516,9,34,64,128,16] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 160 96 208 464 720), lower := (rows 273 518 13 42 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 518 13 10 977 128 977 128 256 512) }] }

theorem upper_18 : Upper D R [272,516,9,34,64,128,32] 13 :=
  bound_sound D R [272,516,9,34,64,128,32] 13 bound_18
    ((Boolean.boundCheck_true D R [272,516,9,34,64,128,32] 13 bound_18).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 160 192 144 352 608), lower := (rows 273 518 13 42 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 224 224 128 504 760), good := (rows 769 518 783 874 864 992 992 992 256 512) }] }

theorem upper_20 : Upper D R [272,516,9,34,64,128,128,16] 13 :=
  bound_sound D R [272,516,9,34,64,128,128,16] 13 bound_20
    ((Boolean.boundCheck_true D R [272,516,9,34,64,128,128,16] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 160 192 160 336 592), lower := (rows 273 518 13 42 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 750 237 234 224 224 224 224 480 736) }] }

theorem upper_21 : Upper D R [272,516,9,34,64,128,128,32] 13 :=
  bound_sound D R [272,516,9,34,64,128,128,32] 13 bound_21
    ((Boolean.boundCheck_true D R [272,516,9,34,64,128,128,32] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 13 42 80 160 192 192 304 560), lower := (rows 273 518 13 42 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 750 237 234 224 224 224 224 480 736) }] }

theorem upper_22 : Upper D R [272,516,9,34,64,128,128,64] 13 :=
  bound_sound D R [272,516,9,34,64,128,128,64] 13 bound_22
    ((Boolean.boundCheck_true D R [272,516,9,34,64,128,128,64] 13 bound_22).mp (by decide +kernel))

def route_19 : Route 10 := (fun mask => (mask,id))

theorem upper_19 : Upper D R [272,516,9,34,64,128,128] 13 := by
  apply routed_branch D R [272,516,9,34,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_19
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34,64,128,128] (choices 1) [16,32,64] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_20
  · exact upper_21
  · exact upper_22

def route_16 : Route 10 := (fun mask => (mask,id))

theorem upper_16 : Upper D R [272,516,9,34,64,128] 13 := by
  apply routed_branch D R [272,516,9,34,64,128] 13 (by decide) (choices 1) [16,32,128] route_16
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34,64,128] (choices 1) [16,32,128] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_17
  · exact upper_18
  · exact upper_19

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [272,516,9,34,64] 13 := by
  apply routed_branch D R [272,516,9,34,64] 13 (by decide) (choices 1) [16,64,128] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34,64] (choices 1) [16,64,128] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_9
  · exact upper_10
  · exact upper_16

def route_6 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_6 : Upper D R [272,516,9,34] 13 := by
  apply routed_branch D R [272,516,9,34] 13 (by decide) (choices 1) [32,64] route_6
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,9,34] (choices 1) [32,64] route_6).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_7
  · exact upper_8

def bound_23 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 13 56 242 226 226 226 482 738), lower := (rows 273 518 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [272,516,9,48] 13 :=
  bound_sound D R [272,516,9,48] 13 bound_23
    ((Boolean.boundCheck_true D R [272,516,9,48] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 518 13 104 242 242 242 242 498 754), lower := (rows 273 518 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [272,516,9,96] 13 :=
  bound_sound D R [272,516,9,96] 13 bound_24
    ((Boolean.boundCheck_true D R [272,516,9,96] 13 bound_24).mp (by decide +kernel))

def route_4 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_4 : Upper D R [272,516,9] 13 := by
  apply routed_branch D R [272,516,9] 13 (by decide) (choices 2) [18,34,48,96] route_4
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,9] (choices 2) [18,34,48,96] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_5
  · exact upper_6
  · exact upper_23
  · exact upper_24

def bound_26 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 273 518 14 25 240 224 224 224 480 736), lower := (rows 273 518 14 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 1023 1023 1023 1023 1023), good := (rows 993 998 1006 1007 992 992 992 992 992 992) }] }

theorem upper_26 : Upper D R [272,516,10,17] 13 :=
  bound_sound D R [272,516,10,17] 13 bound_26
    ((Boolean.boundCheck_true D R [272,516,10,17] 13 bound_26).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 273 518 14 41 48 240 208 208 464 720), lower := (rows 273 518 14 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 10 12 8 16 0 81 145 273 529), good := (rows 977 518 14 975 977 0 64 128 256 512) }] }

theorem upper_28 : Upper D R [272,516,10,33,32] 13 :=
  bound_sound D R [272,516,10,33,32] 13 bound_28
    ((Boolean.boundCheck_true D R [272,516,10,33,32] 13 bound_28).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 48 224 224 480 736), lower := (rows 273 518 14 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 32 104 168 296 552), good := (rows 257 518 974 1007 64 992 64 128 256 512) }] }

theorem upper_30 : Upper D R [272,516,10,33,64,16] 13 :=
  bound_sound D R [272,516,10,33,64,16] 13 bound_30
    ((Boolean.boundCheck_true D R [272,516,10,33,64,16] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 96 240 176 432 688), lower := (rows 273 518 14 41 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 112 64 128 256 512), good := (rows 297 518 14 41 96 96 96 128 256 512) }] }

theorem upper_31 : Upper D R [272,516,10,33,64,64] 13 :=
  bound_sound D R [272,516,10,33,64,64] 13 bound_31
    ((Boolean.boundCheck_true D R [272,516,10,33,64,64] 13 bound_31).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 160 80 224 480 736), lower := (rows 273 518 14 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 13 9 0 241 64 208 336 592), good := (rows 943 518 14 47 992 160 992 160 256 512) }] }

theorem upper_33 : Upper D R [272,516,10,33,64,128,16] 13 :=
  bound_sound D R [272,516,10,33,64,128,16] 13 bound_33
    ((Boolean.boundCheck_true D R [272,516,10,33,64,128,16] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 160 96 208 464 720), lower := (rows 273 518 14 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 518 14 9 977 128 977 128 256 512) }] }

theorem upper_34 : Upper D R [272,516,10,33,64,128,32] 13 :=
  bound_sound D R [272,516,10,33,64,128,32] 13 bound_34
    ((Boolean.boundCheck_true D R [272,516,10,33,64,128,32] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 160 192 144 352 608), lower := (rows 273 518 14 41 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 14 12 8 0 224 224 128 504 760), good := (rows 769 518 782 879 864 992 992 992 256 512) }] }

theorem upper_36 : Upper D R [272,516,10,33,64,128,128,16] 13 :=
  bound_sound D R [272,516,10,33,64,128,128,16] 13 bound_36
    ((Boolean.boundCheck_true D R [272,516,10,33,64,128,128,16] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 160 192 160 336 592), lower := (rows 273 518 14 41 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 489 742 238 233 224 224 224 224 480 736) }] }

theorem upper_37 : Upper D R [272,516,10,33,64,128,128,32] 13 :=
  bound_sound D R [272,516,10,33,64,128,128,32] 13 bound_37
    ((Boolean.boundCheck_true D R [272,516,10,33,64,128,128,32] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 14 41 80 160 192 192 304 560), lower := (rows 273 518 14 41 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 489 742 238 233 224 224 224 224 480 736) }] }

theorem upper_38 : Upper D R [272,516,10,33,64,128,128,64] 13 :=
  bound_sound D R [272,516,10,33,64,128,128,64] 13 bound_38
    ((Boolean.boundCheck_true D R [272,516,10,33,64,128,128,64] 13 bound_38).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => (mask,id))

theorem upper_35 : Upper D R [272,516,10,33,64,128,128] 13 := by
  apply routed_branch D R [272,516,10,33,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,10,33,64,128,128] (choices 1) [16,32,64] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_36
  · exact upper_37
  · exact upper_38

def route_32 : Route 10 := (fun mask => (mask,id))

theorem upper_32 : Upper D R [272,516,10,33,64,128] 13 := by
  apply routed_branch D R [272,516,10,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,10,33,64,128] (choices 1) [16,32,128] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_35

def route_29 : Route 10 := (fun mask => (mask,id))

theorem upper_29 : Upper D R [272,516,10,33,64] 13 := by
  apply routed_branch D R [272,516,10,33,64] 13 (by decide) (choices 1) [16,64,128] route_29
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,10,33,64] (choices 1) [16,64,128] route_29).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_30
  · exact upper_31
  · exact upper_32

def route_27 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_27 : Upper D R [272,516,10,33] 13 := by
  apply routed_branch D R [272,516,10,33] 13 (by decide) (choices 1) [32,64] route_27
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,10,33] (choices 1) [32,64] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_28
  · exact upper_29

def bound_39 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 518 14 56 241 225 225 225 481 737), lower := (rows 273 518 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [272,516,10,48] 13 :=
  bound_sound D R [272,516,10,48] 13 bound_39
    ((Boolean.boundCheck_true D R [272,516,10,48] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 518 14 104 241 241 241 241 497 753), lower := (rows 273 518 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [272,516,10,96] 13 :=
  bound_sound D R [272,516,10,96] 13 bound_40
    ((Boolean.boundCheck_true D R [272,516,10,96] 13 bound_40).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [272,516,10] 13 := by
  apply routed_branch D R [272,516,10] 13 (by decide) (choices 2) [17,33,48,96] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,10] (choices 2) [17,33,48,96] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_39
  · exact upper_40

def bound_42 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 518 21 42 248 232 232 232 488 744), lower := (rows 273 518 21 42 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [272,516,17,34] 13 :=
  bound_sound D R [272,516,17,34] 13 bound_42
    ((Boolean.boundCheck_true D R [272,516,17,34] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 518 21 104 250 234 234 234 490 746), lower := (rows 273 518 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [272,516,17,96] 13 :=
  bound_sound D R [272,516,17,96] 13 bound_43
    ((Boolean.boundCheck_true D R [272,516,17,96] 13 bound_43).mp (by decide +kernel))

def route_41 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_41 : Upper D R [272,516,17] 13 := by
  apply routed_branch D R [272,516,17] 13 (by decide) (choices 2) [34,96] route_41
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,17] (choices 2) [34,96] route_41).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_42
  · exact upper_43

def bound_45 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 518 22 41 248 232 232 232 488 744), lower := (rows 273 518 22 41 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [272,516,18,33] 13 :=
  bound_sound D R [272,516,18,33] 13 bound_45
    ((Boolean.boundCheck_true D R [272,516,18,33] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 518 22 104 249 233 233 233 489 745), lower := (rows 273 518 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [272,516,18,96] 13 :=
  bound_sound D R [272,516,18,96] 13 bound_46
    ((Boolean.boundCheck_true D R [272,516,18,96] 13 bound_46).mp (by decide +kernel))

def route_44 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_44 : Upper D R [272,516,18] 13 := by
  apply routed_branch D R [272,516,18] 13 (by decide) (choices 2) [33,96] route_44
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,18] (choices 2) [33,96] route_44).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_45
  · exact upper_46

def bound_48 : Bound 10 := { allowed := (rows 224 224 224 240 0 0 0 0 0 0), upper := (rows 273 518 28 11 240 224 224 224 480 736), lower := (rows 273 518 28 11 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 998 1006 1003 992 992 992 992 992 992) }] }

theorem upper_48 : Upper D R [272,516,24,3] 13 :=
  bound_sound D R [272,516,24,3] 13 bound_48
    ((Boolean.boundCheck_true D R [272,516,24,3] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 518 28 41 242 226 226 226 482 738), lower := (rows 273 518 28 41 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [272,516,24,33] 13 :=
  bound_sound D R [272,516,24,33] 13 bound_49
    ((Boolean.boundCheck_true D R [272,516,24,33] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 518 28 42 241 225 225 225 481 737), lower := (rows 273 518 28 42 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [272,516,24,34] 13 :=
  bound_sound D R [272,516,24,34] 13 bound_50
    ((Boolean.boundCheck_true D R [272,516,24,34] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 518 28 104 243 227 227 227 483 739), lower := (rows 273 518 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [272,516,24,96] 13 :=
  bound_sound D R [272,516,24,96] 13 bound_51
    ((Boolean.boundCheck_true D R [272,516,24,96] 13 bound_51).mp (by decide +kernel))

def route_47 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_47 : Upper D R [272,516,24] 13 := by
  apply routed_branch D R [272,516,24] 13 (by decide) (choices 2) [3,33,34,96] route_47
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,24] (choices 2) [3,33,34,96] route_47).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51

def bound_53 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 518 37 26 248 232 232 232 488 744), lower := (rows 273 518 37 26 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [272,516,33,18] 13 :=
  bound_sound D R [272,516,33,18] 13 bound_53
    ((Boolean.boundCheck_true D R [272,516,33,18] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 518 37 42 216 248 216 216 472 728), lower := (rows 273 518 37 42 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [272,516,33,34] 13 :=
  bound_sound D R [272,516,33,34] 13 bound_54
    ((Boolean.boundCheck_true D R [272,516,33,34] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 518 37 56 218 234 202 202 458 714), lower := (rows 273 518 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [272,516,33,48] 13 :=
  bound_sound D R [272,516,33,48] 13 bound_55
    ((Boolean.boundCheck_true D R [272,516,33,48] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 518 37 74 248 248 248 248 504 760), lower := (rows 273 518 37 74 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [272,516,33,66] 13 :=
  bound_sound D R [272,516,33,66] 13 bound_56
    ((Boolean.boundCheck_true D R [272,516,33,66] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 518 37 88 250 234 234 234 490 746), lower := (rows 273 518 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [272,516,33,80] 13 :=
  bound_sound D R [272,516,33,80] 13 bound_57
    ((Boolean.boundCheck_true D R [272,516,33,80] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 518 37 104 218 250 218 218 474 730), lower := (rows 273 518 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [272,516,33,96] 13 :=
  bound_sound D R [272,516,33,96] 13 bound_58
    ((Boolean.boundCheck_true D R [272,516,33,96] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 518 37 200 250 250 250 250 506 762), lower := (rows 273 518 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [272,516,33,192] 13 :=
  bound_sound D R [272,516,33,192] 13 bound_59
    ((Boolean.boundCheck_true D R [272,516,33,192] 13 bound_59).mp (by decide +kernel))

def route_52 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_52 : Upper D R [272,516,33] 13 := by
  apply routed_branch D R [272,516,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] route_52
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,33] (choices 2) [18,34,48,66,80,96,192] route_52).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_53
  · exact upper_54
  · exact upper_55
  · exact upper_56
  · exact upper_57
  · exact upper_58
  · exact upper_59

def bound_61 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 518 38 25 248 232 232 232 488 744), lower := (rows 273 518 38 25 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [272,516,34,17] 13 :=
  bound_sound D R [272,516,34,17] 13 bound_61
    ((Boolean.boundCheck_true D R [272,516,34,17] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 518 38 41 216 248 216 216 472 728), lower := (rows 273 518 38 41 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [272,516,34,33] 13 :=
  bound_sound D R [272,516,34,33] 13 bound_62
    ((Boolean.boundCheck_true D R [272,516,34,33] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 518 38 56 217 233 201 201 457 713), lower := (rows 273 518 38 56 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [272,516,34,48] 13 :=
  bound_sound D R [272,516,34,48] 13 bound_63
    ((Boolean.boundCheck_true D R [272,516,34,48] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 518 38 73 248 248 248 248 504 760), lower := (rows 273 518 38 73 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [272,516,34,65] 13 :=
  bound_sound D R [272,516,34,65] 13 bound_64
    ((Boolean.boundCheck_true D R [272,516,34,65] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 518 38 88 249 233 233 233 489 745), lower := (rows 273 518 38 88 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [272,516,34,80] 13 :=
  bound_sound D R [272,516,34,80] 13 bound_65
    ((Boolean.boundCheck_true D R [272,516,34,80] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 518 38 104 217 249 217 217 473 729), lower := (rows 273 518 38 104 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [272,516,34,96] 13 :=
  bound_sound D R [272,516,34,96] 13 bound_66
    ((Boolean.boundCheck_true D R [272,516,34,96] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 518 38 200 249 249 249 249 505 761), lower := (rows 273 518 38 200 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [272,516,34,192] 13 :=
  bound_sound D R [272,516,34,192] 13 bound_67
    ((Boolean.boundCheck_true D R [272,516,34,192] 13 bound_67).mp (by decide +kernel))

def route_60 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_60 : Upper D R [272,516,34] 13 := by
  apply routed_branch D R [272,516,34] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] route_60
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,34] (choices 2) [17,33,48,65,80,96,192] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_61
  · exact upper_62
  · exact upper_63
  · exact upper_64
  · exact upper_65
  · exact upper_66
  · exact upper_67

def bound_70 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 48 240 208 208 464 720), lower := (rows 273 518 44 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 518 12 971 977 0 64 128 256 512) }] }

theorem upper_70 : Upper D R [272,516,40,3,32] 13 :=
  bound_sound D R [272,516,40,3,32] 13 bound_70
    ((Boolean.boundCheck_true D R [272,516,40,3,32] 13 bound_70).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 48 224 224 480 736), lower := (rows 273 518 44 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 100 164 292 548), good := (rows 257 966 1006 11 64 992 64 128 256 512) }] }

theorem upper_72 : Upper D R [272,516,40,3,64,16] 13 :=
  bound_sound D R [272,516,40,3,64,16] 13 bound_72
    ((Boolean.boundCheck_true D R [272,516,40,3,64,16] 13 bound_72).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 96 80 160 416 672), lower := (rows 273 518 44 11 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 15 5 9 0 112 64 245 373 629), good := (rows 943 902 942 911 992 992 992 128 256 512) }] }

theorem upper_74 : Upper D R [272,516,40,3,64,64,16] 13 :=
  bound_sound D R [272,516,40,3,64,64,16] 13 bound_74
    ((Boolean.boundCheck_true D R [272,516,40,3,64,64,16] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 96 96 144 400 656), lower := (rows 273 518 44 11 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 128 256 512), good := (rows 353 614 108 111 96 96 96 224 352 608) }] }

theorem upper_75 : Upper D R [272,516,40,3,64,64,32] 13 :=
  bound_sound D R [272,516,40,3,64,64,32] 13 bound_75
    ((Boolean.boundCheck_true D R [272,516,40,3,64,64,32] 13 bound_75).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 96 192 144 416 672), lower := (rows 273 518 44 11 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 726 220 219 208 208 208 208 465 720) }] }

theorem upper_77 : Upper D R [272,516,40,3,64,64,128,16] 13 :=
  bound_sound D R [272,516,40,3,64,64,128,16] 13 bound_77
    ((Boolean.boundCheck_true D R [272,516,40,3,64,64,128,16] 13 bound_77).mp (by decide +kernel))

def bound_78 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 96 192 160 400 656), lower := (rows 273 518 44 11 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 742 236 239 224 224 224 224 480 736) }] }

theorem upper_78 : Upper D R [272,516,40,3,64,64,128,32] 13 :=
  bound_sound D R [272,516,40,3,64,64,128,32] 13 bound_78
    ((Boolean.boundCheck_true D R [272,516,40,3,64,64,128,32] 13 bound_78).mp (by decide +kernel))

def route_76 : Route 10 := (fun mask => (mask,id))

theorem upper_76 : Upper D R [272,516,40,3,64,64,128] 13 := by
  apply routed_branch D R [272,516,40,3,64,64,128] 13 (by decide) (choices 1) [16,32] route_76
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3,64,64,128] (choices 1) [16,32] route_76).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_77
  · exact upper_78

def route_73 : Route 10 := (fun mask => (mask,id))

theorem upper_73 : Upper D R [272,516,40,3,64,64] 13 := by
  apply routed_branch D R [272,516,40,3,64,64] 13 (by decide) (choices 1) [16,32,128] route_73
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3,64,64] (choices 1) [16,32,128] route_73).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_74
  · exact upper_75
  · exact upper_76

def bound_80 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 160 80 224 480 736), lower := (rows 273 518 44 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 13 9 0 241 64 208 336 592), good := (rows 943 518 44 47 992 160 992 160 256 512) }] }

theorem upper_80 : Upper D R [272,516,40,3,64,128,16] 13 :=
  bound_sound D R [272,516,40,3,64,128,16] 13 bound_80
    ((Boolean.boundCheck_true D R [272,516,40,3,64,128,16] 13 bound_80).mp (by decide +kernel))

def bound_81 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 160 96 208 464 720), lower := (rows 273 518 44 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 518 12 11 977 128 977 128 256 512) }] }

theorem upper_81 : Upper D R [272,516,40,3,64,128,32] 13 :=
  bound_sound D R [272,516,40,3,64,128,32] 13 bound_81
    ((Boolean.boundCheck_true D R [272,516,40,3,64,128,32] 13 bound_81).mp (by decide +kernel))

def bound_83 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 160 192 144 352 608), lower := (rows 273 518 44 11 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 6 4 8 0 224 224 128 500 756), good := (rows 769 774 878 11 864 992 992 992 256 512) }] }

theorem upper_83 : Upper D R [272,516,40,3,64,128,128,16] 13 :=
  bound_sound D R [272,516,40,3,64,128,128,16] 13 bound_83
    ((Boolean.boundCheck_true D R [272,516,40,3,64,128,128,16] 13 bound_83).mp (by decide +kernel))

def bound_84 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 160 192 160 336 592), lower := (rows 273 518 44 11 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 742 236 239 224 224 224 224 480 736) }] }

theorem upper_84 : Upper D R [272,516,40,3,64,128,128,32] 13 :=
  bound_sound D R [272,516,40,3,64,128,128,32] 13 bound_84
    ((Boolean.boundCheck_true D R [272,516,40,3,64,128,128,32] 13 bound_84).mp (by decide +kernel))

def bound_85 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 518 44 11 80 160 192 192 304 560), lower := (rows 273 518 44 11 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 742 236 239 224 224 224 224 480 736) }] }

theorem upper_85 : Upper D R [272,516,40,3,64,128,128,64] 13 :=
  bound_sound D R [272,516,40,3,64,128,128,64] 13 bound_85
    ((Boolean.boundCheck_true D R [272,516,40,3,64,128,128,64] 13 bound_85).mp (by decide +kernel))

def route_82 : Route 10 := (fun mask => (mask,id))

theorem upper_82 : Upper D R [272,516,40,3,64,128,128] 13 := by
  apply routed_branch D R [272,516,40,3,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_82
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3,64,128,128] (choices 1) [16,32,64] route_82).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_83
  · exact upper_84
  · exact upper_85

def route_79 : Route 10 := (fun mask => (mask,id))

theorem upper_79 : Upper D R [272,516,40,3,64,128] 13 := by
  apply routed_branch D R [272,516,40,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_79
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3,64,128] (choices 1) [16,32,128] route_79).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_80
  · exact upper_81
  · exact upper_82

def route_71 : Route 10 := (fun mask => (mask,id))

theorem upper_71 : Upper D R [272,516,40,3,64] 13 := by
  apply routed_branch D R [272,516,40,3,64] 13 (by decide) (choices 1) [16,64,128] route_71
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3,64] (choices 1) [16,64,128] route_71).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_72
  · exact upper_73
  · exact upper_79

def route_69 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_69 : Upper D R [272,516,40,3] 13 := by
  apply routed_branch D R [272,516,40,3] 13 (by decide) (choices 1) [32,64] route_69
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,516,40,3] (choices 1) [32,64] route_69).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_70
  · exact upper_71

def bound_86 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 518 44 25 242 226 226 226 482 738), lower := (rows 273 518 44 25 16 32 64 128 256 512), losses := [] }

theorem upper_86 : Upper D R [272,516,40,17] 13 :=
  bound_sound D R [272,516,40,17] 13 bound_86
    ((Boolean.boundCheck_true D R [272,516,40,17] 13 bound_86).mp (by decide +kernel))

def bound_87 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 518 44 26 241 225 225 225 481 737), lower := (rows 273 518 44 26 16 32 64 128 256 512), losses := [] }

theorem upper_87 : Upper D R [272,516,40,18] 13 :=
  bound_sound D R [272,516,40,18] 13 bound_87
    ((Boolean.boundCheck_true D R [272,516,40,18] 13 bound_87).mp (by decide +kernel))

def bound_88 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 518 44 41 210 242 210 210 466 722), lower := (rows 273 518 44 41 16 32 64 128 256 512), losses := [] }

theorem upper_88 : Upper D R [272,516,40,33] 13 :=
  bound_sound D R [272,516,40,33] 13 bound_88
    ((Boolean.boundCheck_true D R [272,516,40,33] 13 bound_88).mp (by decide +kernel))

def bound_89 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 518 44 42 209 241 209 209 465 721), lower := (rows 273 518 44 42 16 32 64 128 256 512), losses := [] }

theorem upper_89 : Upper D R [272,516,40,34] 13 :=
  bound_sound D R [272,516,40,34] 13 bound_89
    ((Boolean.boundCheck_true D R [272,516,40,34] 13 bound_89).mp (by decide +kernel))

def bound_90 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 518 44 56 211 227 195 195 451 707), lower := (rows 273 518 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_90 : Upper D R [272,516,40,48] 13 :=
  bound_sound D R [272,516,40,48] 13 bound_90
    ((Boolean.boundCheck_true D R [272,516,40,48] 13 bound_90).mp (by decide +kernel))

def bound_91 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 518 44 73 242 242 242 242 498 754), lower := (rows 273 518 44 73 16 32 64 128 256 512), losses := [] }

theorem upper_91 : Upper D R [272,516,40,65] 13 :=
  bound_sound D R [272,516,40,65] 13 bound_91
    ((Boolean.boundCheck_true D R [272,516,40,65] 13 bound_91).mp (by decide +kernel))

def bound_92 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 518 44 74 241 241 241 241 497 753), lower := (rows 273 518 44 74 16 32 64 128 256 512), losses := [] }

theorem upper_92 : Upper D R [272,516,40,66] 13 :=
  bound_sound D R [272,516,40,66] 13 bound_92
    ((Boolean.boundCheck_true D R [272,516,40,66] 13 bound_92).mp (by decide +kernel))

def bound_93 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 518 44 88 243 227 227 227 483 739), lower := (rows 273 518 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_93 : Upper D R [272,516,40,80] 13 :=
  bound_sound D R [272,516,40,80] 13 bound_93
    ((Boolean.boundCheck_true D R [272,516,40,80] 13 bound_93).mp (by decide +kernel))

def bound_94 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 518 44 104 211 243 211 211 467 723), lower := (rows 273 518 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_94 : Upper D R [272,516,40,96] 13 :=
  bound_sound D R [272,516,40,96] 13 bound_94
    ((Boolean.boundCheck_true D R [272,516,40,96] 13 bound_94).mp (by decide +kernel))

def bound_95 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 518 44 200 243 243 243 243 499 755), lower := (rows 273 518 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_95 : Upper D R [272,516,40,192] 13 :=
  bound_sound D R [272,516,40,192] 13 bound_95
    ((Boolean.boundCheck_true D R [272,516,40,192] 13 bound_95).mp (by decide +kernel))

def route_68 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_68 : Upper D R [272,516,40] 13 := by
  apply routed_branch D R [272,516,40] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_68
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516,40] (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_68).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_69
  · exact upper_86
  · exact upper_87
  · exact upper_88
  · exact upper_89
  · exact upper_90
  · exact upper_91
  · exact upper_92
  · exact upper_93
  · exact upper_94
  · exact upper_95

def bound_96 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 518 52 235 251 235 235 235 491 747), lower := (rows 273 518 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_96 : Upper D R [272,516,48] 13 :=
  bound_sound D R [272,516,48] 13 bound_96
    ((Boolean.boundCheck_true D R [272,516,48] 13 bound_96).mp (by decide +kernel))

def bound_97 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 273 518 100 251 251 251 251 251 507 763), lower := (rows 273 518 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_97 : Upper D R [272,516,96] 13 :=
  bound_sound D R [272,516,96] 13 bound_97
    ((Boolean.boundCheck_true D R [272,516,96] 13 bound_97).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,516] 13 := by
  apply routed_branch D R [272,516] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,96] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,516] (choices 2) [3,9,10,17,18,24,33,34,40,48,96] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_4
  · exact upper_25
  · exact upper_41
  · exact upper_44
  · exact upper_47
  · exact upper_52
  · exact upper_60
  · exact upper_68
  · exact upper_96
  · exact upper_97

theorem upper : Upper D R [272,516] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case52
