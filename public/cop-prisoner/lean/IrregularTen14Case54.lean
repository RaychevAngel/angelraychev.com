import IrregularTen14Base

namespace Delivery.IrregularTen14.Case54
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 546 7 28 248 232 232 232 488 744), lower := (rows 273 546 7 28 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,544,3,20] 13 :=
  bound_sound D R [272,544,3,20] 13 bound_2
    ((Boolean.boundCheck_true D R [272,544,3,20] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 546 7 44 216 248 216 216 472 728), lower := (rows 273 546 7 44 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,544,3,36] 13 :=
  bound_sound D R [272,544,3,36] 13 bound_3
    ((Boolean.boundCheck_true D R [272,544,3,36] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 546 7 56 220 236 204 204 460 716), lower := (rows 273 546 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [272,544,3,48] 13 :=
  bound_sound D R [272,544,3,48] 13 bound_4
    ((Boolean.boundCheck_true D R [272,544,3,48] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 546 7 76 248 248 248 248 504 760), lower := (rows 273 546 7 76 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [272,544,3,68] 13 :=
  bound_sound D R [272,544,3,68] 13 bound_5
    ((Boolean.boundCheck_true D R [272,544,3,68] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 546 7 88 252 236 236 236 492 748), lower := (rows 273 546 7 88 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [272,544,3,80] 13 :=
  bound_sound D R [272,544,3,80] 13 bound_6
    ((Boolean.boundCheck_true D R [272,544,3,80] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 546 7 104 220 252 220 220 476 732), lower := (rows 273 546 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [272,544,3,96] 13 :=
  bound_sound D R [272,544,3,96] 13 bound_7
    ((Boolean.boundCheck_true D R [272,544,3,96] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 546 7 200 252 252 252 252 508 764), lower := (rows 273 546 7 200 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [272,544,3,192] 13 :=
  bound_sound D R [272,544,3,192] 13 bound_8
    ((Boolean.boundCheck_true D R [272,544,3,192] 13 bound_8).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,544,3] 13 := by
  apply routed_branch D R [272,544,3] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,544,3] (choices 2) [20,36,48,68,80,96,192] route_1).mp (by decide +kernel))
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

def bound_11 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 48 240 208 208 464 720), lower := (rows 273 546 13 14 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 514 973 14 977 0 64 128 256 512) }] }

theorem upper_11 : Upper D R [272,544,9,6,32] 13 :=
  bound_sound D R [272,544,9,6,32] 13 bound_11
    ((Boolean.boundCheck_true D R [272,544,9,6,32] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 48 224 224 480 736), lower := (rows 273 546 13 14 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 98 162 290 546), good := (rows 257 994 13 974 64 994 64 128 256 512) }] }

theorem upper_13 : Upper D R [272,544,9,6,64,16] 13 :=
  bound_sound D R [272,544,9,6,64,16] 13 bound_13
    ((Boolean.boundCheck_true D R [272,544,9,6,64,16] 13 bound_13).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 96 80 160 416 672), lower := (rows 273 546 13 14 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 115 5 13 0 112 64 243 371 627), good := (rows 943 930 911 910 994 994 994 128 256 512) }] }

theorem upper_15 : Upper D R [272,544,9,6,64,64,16] 13 :=
  bound_sound D R [272,544,9,6,64,64,16] 13 bound_15
    ((Boolean.boundCheck_true D R [272,544,9,6,64,64,16] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 96 96 144 400 656), lower := (rows 273 546 13 14 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 128 256 512), good := (rows 353 610 109 110 96 96 96 224 352 610) }] }

theorem upper_16 : Upper D R [272,544,9,6,64,64,32] 13 :=
  bound_sound D R [272,544,9,6,64,64,32] 13 bound_16
    ((Boolean.boundCheck_true D R [272,544,9,6,64,64,32] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 96 192 144 416 672), lower := (rows 273 546 13 14 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 242 5 9 0 240 192 128 448 704), good := (rows 303 546 13 14 866 866 994 994 256 512) }] }

theorem upper_18 : Upper D R [272,544,9,6,64,64,128,16] 13 :=
  bound_sound D R [272,544,9,6,64,64,128,16] 13 bound_18
    ((Boolean.boundCheck_true D R [272,544,9,6,64,64,128,16] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 96 192 160 400 656), lower := (rows 273 546 13 14 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 237 238 224 224 224 224 480 738) }] }

theorem upper_19 : Upper D R [272,544,9,6,64,64,128,32] 13 :=
  bound_sound D R [272,544,9,6,64,64,128,32] 13 bound_19
    ((Boolean.boundCheck_true D R [272,544,9,6,64,64,128,32] 13 bound_19).mp (by decide +kernel))

def route_17 : Route 10 := (fun mask => (mask,id))

theorem upper_17 : Upper D R [272,544,9,6,64,64,128] 13 := by
  apply routed_branch D R [272,544,9,6,64,64,128] 13 (by decide) (choices 1) [16,32] route_17
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6,64,64,128] (choices 1) [16,32] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_18
  · exact upper_19

def route_14 : Route 10 := (fun mask => (mask,id))

theorem upper_14 : Upper D R [272,544,9,6,64,64] 13 := by
  apply routed_branch D R [272,544,9,6,64,64] 13 (by decide) (choices 1) [16,32,128] route_14
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6,64,64] (choices 1) [16,32,128] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17

def bound_21 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 160 80 224 480 736), lower := (rows 273 546 13 14 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 5 13 0 241 64 208 336 592), good := (rows 943 546 47 14 994 160 994 160 256 512) }] }

theorem upper_21 : Upper D R [272,544,9,6,64,128,16] 13 :=
  bound_sound D R [272,544,9,6,64,128,16] 13 bound_21
    ((Boolean.boundCheck_true D R [272,544,9,6,64,128,16] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 160 96 208 464 720), lower := (rows 273 546 13 14 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 514 13 14 977 128 977 128 256 512) }] }

theorem upper_22 : Upper D R [272,544,9,6,64,128,32] 13 :=
  bound_sound D R [272,544,9,6,64,128,32] 13 bound_22
    ((Boolean.boundCheck_true D R [272,544,9,6,64,128,32] 13 bound_22).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 160 192 144 352 608), lower := (rows 273 546 13 14 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 242 5 9 0 224 224 128 498 754), good := (rows 783 866 13 782 866 994 994 994 256 512) }] }

theorem upper_24 : Upper D R [272,544,9,6,64,128,128,16] 13 :=
  bound_sound D R [272,544,9,6,64,128,128,16] 13 bound_24
    ((Boolean.boundCheck_true D R [272,544,9,6,64,128,128,16] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 160 192 160 336 592), lower := (rows 273 546 13 14 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 237 238 224 224 224 224 480 738) }] }

theorem upper_25 : Upper D R [272,544,9,6,64,128,128,32] 13 :=
  bound_sound D R [272,544,9,6,64,128,128,32] 13 bound_25
    ((Boolean.boundCheck_true D R [272,544,9,6,64,128,128,32] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 13 14 80 160 192 192 304 560), lower := (rows 273 546 13 14 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 237 238 224 224 224 224 480 738) }] }

theorem upper_26 : Upper D R [272,544,9,6,64,128,128,64] 13 :=
  bound_sound D R [272,544,9,6,64,128,128,64] 13 bound_26
    ((Boolean.boundCheck_true D R [272,544,9,6,64,128,128,64] 13 bound_26).mp (by decide +kernel))

def route_23 : Route 10 := (fun mask => (mask,id))

theorem upper_23 : Upper D R [272,544,9,6,64,128,128] 13 := by
  apply routed_branch D R [272,544,9,6,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_23
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6,64,128,128] (choices 1) [16,32,64] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_24
  · exact upper_25
  · exact upper_26

def route_20 : Route 10 := (fun mask => (mask,id))

theorem upper_20 : Upper D R [272,544,9,6,64,128] 13 := by
  apply routed_branch D R [272,544,9,6,64,128] 13 (by decide) (choices 1) [16,32,128] route_20
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6,64,128] (choices 1) [16,32,128] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_21
  · exact upper_22
  · exact upper_23

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [272,544,9,6,64] 13 := by
  apply routed_branch D R [272,544,9,6,64] 13 (by decide) (choices 1) [16,64,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6,64] (choices 1) [16,64,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_20

def route_10 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_10 : Upper D R [272,544,9,6] 13 := by
  apply routed_branch D R [272,544,9,6] 13 (by decide) (choices 1) [32,64] route_10
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,9,6] (choices 1) [32,64] route_10).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_11
  · exact upper_12

def bound_27 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 546 13 26 244 228 228 228 484 740), lower := (rows 273 546 13 26 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [272,544,9,18] 13 :=
  bound_sound D R [272,544,9,18] 13 bound_27
    ((Boolean.boundCheck_true D R [272,544,9,18] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 546 13 28 242 226 226 226 482 738), lower := (rows 273 546 13 28 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [272,544,9,20] 13 :=
  bound_sound D R [272,544,9,20] 13 bound_28
    ((Boolean.boundCheck_true D R [272,544,9,20] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 546 13 42 212 244 212 212 468 724), lower := (rows 273 546 13 42 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [272,544,9,34] 13 :=
  bound_sound D R [272,544,9,34] 13 bound_29
    ((Boolean.boundCheck_true D R [272,544,9,34] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 546 13 44 210 242 210 210 466 722), lower := (rows 273 546 13 44 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [272,544,9,36] 13 :=
  bound_sound D R [272,544,9,36] 13 bound_30
    ((Boolean.boundCheck_true D R [272,544,9,36] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 546 13 56 214 230 198 198 454 710), lower := (rows 273 546 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [272,544,9,48] 13 :=
  bound_sound D R [272,544,9,48] 13 bound_31
    ((Boolean.boundCheck_true D R [272,544,9,48] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 546 13 74 244 244 244 244 500 756), lower := (rows 273 546 13 74 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [272,544,9,66] 13 :=
  bound_sound D R [272,544,9,66] 13 bound_32
    ((Boolean.boundCheck_true D R [272,544,9,66] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 546 13 76 242 242 242 242 498 754), lower := (rows 273 546 13 76 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [272,544,9,68] 13 :=
  bound_sound D R [272,544,9,68] 13 bound_33
    ((Boolean.boundCheck_true D R [272,544,9,68] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 546 13 88 246 230 230 230 486 742), lower := (rows 273 546 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [272,544,9,80] 13 :=
  bound_sound D R [272,544,9,80] 13 bound_34
    ((Boolean.boundCheck_true D R [272,544,9,80] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 546 13 104 214 246 214 214 470 726), lower := (rows 273 546 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [272,544,9,96] 13 :=
  bound_sound D R [272,544,9,96] 13 bound_35
    ((Boolean.boundCheck_true D R [272,544,9,96] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 546 13 200 246 246 246 246 502 758), lower := (rows 273 546 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,544,9,192] 13 :=
  bound_sound D R [272,544,9,192] 13 bound_36
    ((Boolean.boundCheck_true D R [272,544,9,192] 13 bound_36).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [272,544,9] 13 := by
  apply routed_branch D R [272,544,9] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_9
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,544,9] (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_10
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_35
  · exact upper_36

def bound_39 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 48 240 208 208 464 720), lower := (rows 273 546 14 13 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 514 14 973 977 0 64 128 256 512) }] }

theorem upper_39 : Upper D R [272,544,10,5,32] 13 :=
  bound_sound D R [272,544,10,5,32] 13 bound_39
    ((Boolean.boundCheck_true D R [272,544,10,5,32] 13 bound_39).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 48 224 224 480 736), lower := (rows 273 546 14 13 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 98 162 290 546), good := (rows 257 994 974 13 64 994 64 128 256 512) }] }

theorem upper_41 : Upper D R [272,544,10,5,64,16] 13 :=
  bound_sound D R [272,544,10,5,64,16] 13 bound_41
    ((Boolean.boundCheck_true D R [272,544,10,5,64,16] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 96 80 160 416 672), lower := (rows 273 546 14 13 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 115 13 9 0 112 64 243 371 627), good := (rows 943 930 910 911 994 994 994 128 256 512) }] }

theorem upper_43 : Upper D R [272,544,10,5,64,64,16] 13 :=
  bound_sound D R [272,544,10,5,64,64,16] 13 bound_43
    ((Boolean.boundCheck_true D R [272,544,10,5,64,64,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 96 96 144 400 656), lower := (rows 273 546 14 13 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 128 256 512), good := (rows 353 610 110 109 96 96 96 224 352 610) }] }

theorem upper_44 : Upper D R [272,544,10,5,64,64,32] 13 :=
  bound_sound D R [272,544,10,5,64,64,32] 13 bound_44
    ((Boolean.boundCheck_true D R [272,544,10,5,64,64,32] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 96 192 144 416 672), lower := (rows 273 546 14 13 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 242 5 9 0 240 192 128 448 704), good := (rows 303 546 14 13 866 866 994 994 256 512) }] }

theorem upper_46 : Upper D R [272,544,10,5,64,64,128,16] 13 :=
  bound_sound D R [272,544,10,5,64,64,128,16] 13 bound_46
    ((Boolean.boundCheck_true D R [272,544,10,5,64,64,128,16] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 96 192 160 400 656), lower := (rows 273 546 14 13 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 238 237 224 224 224 224 480 738) }] }

theorem upper_47 : Upper D R [272,544,10,5,64,64,128,32] 13 :=
  bound_sound D R [272,544,10,5,64,64,128,32] 13 bound_47
    ((Boolean.boundCheck_true D R [272,544,10,5,64,64,128,32] 13 bound_47).mp (by decide +kernel))

def route_45 : Route 10 := (fun mask => (mask,id))

theorem upper_45 : Upper D R [272,544,10,5,64,64,128] 13 := by
  apply routed_branch D R [272,544,10,5,64,64,128] 13 (by decide) (choices 1) [16,32] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5,64,64,128] (choices 1) [16,32] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_46
  · exact upper_47

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [272,544,10,5,64,64] 13 := by
  apply routed_branch D R [272,544,10,5,64,64] 13 (by decide) (choices 1) [16,32,128] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5,64,64] (choices 1) [16,32,128] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def bound_49 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 160 80 224 480 736), lower := (rows 273 546 14 13 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 13 9 0 241 64 208 336 592), good := (rows 943 546 14 47 994 160 994 160 256 512) }] }

theorem upper_49 : Upper D R [272,544,10,5,64,128,16] 13 :=
  bound_sound D R [272,544,10,5,64,128,16] 13 bound_49
    ((Boolean.boundCheck_true D R [272,544,10,5,64,128,16] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 160 96 208 464 720), lower := (rows 273 546 14 13 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 514 14 13 977 128 977 128 256 512) }] }

theorem upper_50 : Upper D R [272,544,10,5,64,128,32] 13 :=
  bound_sound D R [272,544,10,5,64,128,32] 13 bound_50
    ((Boolean.boundCheck_true D R [272,544,10,5,64,128,32] 13 bound_50).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 160 192 144 352 608), lower := (rows 273 546 14 13 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 242 5 9 0 224 224 128 498 754), good := (rows 783 866 782 13 866 994 994 994 256 512) }] }

theorem upper_52 : Upper D R [272,544,10,5,64,128,128,16] 13 :=
  bound_sound D R [272,544,10,5,64,128,128,16] 13 bound_52
    ((Boolean.boundCheck_true D R [272,544,10,5,64,128,128,16] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 160 192 160 336 592), lower := (rows 273 546 14 13 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 238 237 224 224 224 224 480 738) }] }

theorem upper_53 : Upper D R [272,544,10,5,64,128,128,32] 13 :=
  bound_sound D R [272,544,10,5,64,128,128,32] 13 bound_53
    ((Boolean.boundCheck_true D R [272,544,10,5,64,128,128,32] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 273 546 14 13 80 160 192 192 304 560), lower := (rows 273 546 14 13 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 514 4 8 0 1023 1023 1023 256 512), good := (rows 481 738 238 237 224 224 224 224 480 738) }] }

theorem upper_54 : Upper D R [272,544,10,5,64,128,128,64] 13 :=
  bound_sound D R [272,544,10,5,64,128,128,64] 13 bound_54
    ((Boolean.boundCheck_true D R [272,544,10,5,64,128,128,64] 13 bound_54).mp (by decide +kernel))

def route_51 : Route 10 := (fun mask => (mask,id))

theorem upper_51 : Upper D R [272,544,10,5,64,128,128] 13 := by
  apply routed_branch D R [272,544,10,5,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_51
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5,64,128,128] (choices 1) [16,32,64] route_51).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_52
  · exact upper_53
  · exact upper_54

def route_48 : Route 10 := (fun mask => (mask,id))

theorem upper_48 : Upper D R [272,544,10,5,64,128] 13 := by
  apply routed_branch D R [272,544,10,5,64,128] 13 (by decide) (choices 1) [16,32,128] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5,64,128] (choices 1) [16,32,128] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51

def route_40 : Route 10 := (fun mask => (mask,id))

theorem upper_40 : Upper D R [272,544,10,5,64] 13 := by
  apply routed_branch D R [272,544,10,5,64] 13 (by decide) (choices 1) [16,64,128] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5,64] (choices 1) [16,64,128] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_48

def route_38 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_38 : Upper D R [272,544,10,5] 13 := by
  apply routed_branch D R [272,544,10,5] 13 (by decide) (choices 1) [32,64] route_38
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,544,10,5] (choices 1) [32,64] route_38).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_39
  · exact upper_40

def bound_55 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 546 14 25 244 228 228 228 484 740), lower := (rows 273 546 14 25 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [272,544,10,17] 13 :=
  bound_sound D R [272,544,10,17] 13 bound_55
    ((Boolean.boundCheck_true D R [272,544,10,17] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 273 546 14 28 241 225 225 225 481 737), lower := (rows 273 546 14 28 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [272,544,10,20] 13 :=
  bound_sound D R [272,544,10,20] 13 bound_56
    ((Boolean.boundCheck_true D R [272,544,10,20] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 546 14 41 212 244 212 212 468 724), lower := (rows 273 546 14 41 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [272,544,10,33] 13 :=
  bound_sound D R [272,544,10,33] 13 bound_57
    ((Boolean.boundCheck_true D R [272,544,10,33] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 273 546 14 44 209 241 209 209 465 721), lower := (rows 273 546 14 44 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [272,544,10,36] 13 :=
  bound_sound D R [272,544,10,36] 13 bound_58
    ((Boolean.boundCheck_true D R [272,544,10,36] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 273 546 14 56 213 229 197 197 453 709), lower := (rows 273 546 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [272,544,10,48] 13 :=
  bound_sound D R [272,544,10,48] 13 bound_59
    ((Boolean.boundCheck_true D R [272,544,10,48] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 546 14 73 244 244 244 244 500 756), lower := (rows 273 546 14 73 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [272,544,10,65] 13 :=
  bound_sound D R [272,544,10,65] 13 bound_60
    ((Boolean.boundCheck_true D R [272,544,10,65] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 273 546 14 76 241 241 241 241 497 753), lower := (rows 273 546 14 76 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [272,544,10,68] 13 :=
  bound_sound D R [272,544,10,68] 13 bound_61
    ((Boolean.boundCheck_true D R [272,544,10,68] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 273 546 14 88 245 229 229 229 485 741), lower := (rows 273 546 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [272,544,10,80] 13 :=
  bound_sound D R [272,544,10,80] 13 bound_62
    ((Boolean.boundCheck_true D R [272,544,10,80] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 273 546 14 104 213 245 213 213 469 725), lower := (rows 273 546 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [272,544,10,96] 13 :=
  bound_sound D R [272,544,10,96] 13 bound_63
    ((Boolean.boundCheck_true D R [272,544,10,96] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 273 546 14 200 245 245 245 245 501 757), lower := (rows 273 546 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [272,544,10,192] 13 :=
  bound_sound D R [272,544,10,192] 13 bound_64
    ((Boolean.boundCheck_true D R [272,544,10,192] 13 bound_64).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_37 : Upper D R [272,544,10] 13 := by
  apply routed_branch D R [272,544,10] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_37
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,544,10] (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_38
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

def bound_65 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 546 21 238 254 238 238 238 494 750), lower := (rows 273 546 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [272,544,17] 13 :=
  bound_sound D R [272,544,17] 13 bound_65
    ((Boolean.boundCheck_true D R [272,544,17] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 546 22 237 253 237 237 237 493 749), lower := (rows 273 546 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [272,544,18] 13 :=
  bound_sound D R [272,544,18] 13 bound_66
    ((Boolean.boundCheck_true D R [272,544,18] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 273 546 28 239 247 231 231 231 487 743), lower := (rows 273 546 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [272,544,24] 13 :=
  bound_sound D R [272,544,24] 13 bound_67
    ((Boolean.boundCheck_true D R [272,544,24] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 546 37 222 222 254 222 222 478 734), lower := (rows 273 546 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_68 : Upper D R [272,544,33] 13 :=
  bound_sound D R [272,544,33] 13 bound_68
    ((Boolean.boundCheck_true D R [272,544,33] 13 bound_68).mp (by decide +kernel))

def bound_69 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 546 38 221 221 253 221 221 477 733), lower := (rows 273 546 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_69 : Upper D R [272,544,34] 13 :=
  bound_sound D R [272,544,34] 13 bound_69
    ((Boolean.boundCheck_true D R [272,544,34] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 273 546 44 223 215 247 215 215 471 727), lower := (rows 273 546 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [272,544,40] 13 :=
  bound_sound D R [272,544,40] 13 bound_70
    ((Boolean.boundCheck_true D R [272,544,40] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 273 546 52 207 223 239 207 207 463 719), lower := (rows 273 546 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [272,544,48] 13 :=
  bound_sound D R [272,544,48] 13 bound_71
    ((Boolean.boundCheck_true D R [272,544,48] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 546 69 254 254 254 254 254 510 766), lower := (rows 273 546 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [272,544,65] 13 :=
  bound_sound D R [272,544,65] 13 bound_72
    ((Boolean.boundCheck_true D R [272,544,65] 13 bound_72).mp (by decide +kernel))

def bound_73 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 546 70 253 253 253 253 253 509 765), lower := (rows 273 546 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_73 : Upper D R [272,544,66] 13 :=
  bound_sound D R [272,544,66] 13 bound_73
    ((Boolean.boundCheck_true D R [272,544,66] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 273 546 76 255 247 247 247 247 503 759), lower := (rows 273 546 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_74 : Upper D R [272,544,72] 13 :=
  bound_sound D R [272,544,72] 13 bound_74
    ((Boolean.boundCheck_true D R [272,544,72] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 273 546 84 239 255 239 239 239 495 751), lower := (rows 273 546 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_75 : Upper D R [272,544,80] 13 :=
  bound_sound D R [272,544,80] 13 bound_75
    ((Boolean.boundCheck_true D R [272,544,80] 13 bound_75).mp (by decide +kernel))

def bound_76 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 273 546 100 223 223 255 223 223 479 735), lower := (rows 273 546 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_76 : Upper D R [272,544,96] 13 :=
  bound_sound D R [272,544,96] 13 bound_76
    ((Boolean.boundCheck_true D R [272,544,96] 13 bound_76).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 273 546 196 255 255 255 255 255 511 767), lower := (rows 273 546 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_77 : Upper D R [272,544,192] 13 :=
  bound_sound D R [272,544,192] 13 bound_77
    ((Boolean.boundCheck_true D R [272,544,192] 13 bound_77).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,544] 13 := by
  apply routed_branch D R [272,544] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,544] (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem upper : Upper D R [272,544] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case54
