import Std

/-! Finite lower potentials for the two-cardinality relaxation on P_3 cubed.
The checked arrays are merely potentials: optimality of the generator is not
trusted. Neighbor-profile inequalities and the physical bridge are separate.
-/
namespace Princess.ThreeCubeTimeCounter

def profile (p k : Nat) : Nat :=
  if p % 2 = 0 then ([0,3,5,7,8,9,10,10,11,12,12,13,13,13,13] : List Nat).getD k 0
  else ([0,4,6,7,9,10,11,12,12,13,13,14,14,14] : List Nat).getD k 0

def budget (c : Fin 5) : Nat :=
  match c.val with
  | 0 => 5 | 1 => 6 | 2 => 8 | 3 => 11 | _ => 12

def expected (c : Fin 5) : Nat :=
  match c.val with
  | 0 => 18 | 1 => 10 | 2 => 6 | 3 => 4 | _ => 3

def data0 : Nat := 7004945139274080847579266768515790699574473191682374457707523034732113239585349303495304124331309433340200303869907366593615364846593450333556161279194264973407165294745221150855260858602454863948752750471899388365409855860020722664333184625810928982343392345613807125058944115897571307017105309288221298547640796192

def data1 : Nat := 3891269742593642871718092848613710806495428994090472076250624336275984151172630289241410175360816443171640235346553899031068529562374699785987218227021020802981788260298146734688590251350317612364072029524685658495444575633423258013393925982604943737418657625188764477483556074593834223030091832188890367751332332576

def data2 : Nat := 2334609830305097716299794341273331024796668829018585269568880042773176108501480837931690297804214262833387607858969507831034976489540311432236786001451116036234443198980980407470876006916140347536562047867674277721680257635735795744678831725317226745822794025771745963083194044165644240871950955042002851345015538720

def data3 : Nat := 1544498518230847644824419189881694691165741824418367578203289856675680232271098455740142293047664625672597709962156128472847189316896533519269720916129492450896978689382790150590058841210950747947332688840843998482503694439853052454525113830633056733643921979806344626642320575821714625066353698248630019630272906272

def data4 : Nat := 1167494931316903810341928529216931601888137322262788902873323105680377380528935476425425808102903353938226996871353669437856237735359751459291430635717553287522539881397460266374637080355503903045993820900643614393388449758214196667971461069523444935149017311720204260214226612851414015614393316871510905208697816096

def rank (c : Fin 5) (a b : Nat) : Nat :=
  let row := match c.val with
    | 0 => data0 | 1 => data1 | 2 => data2 | 3 => data3 | _ => data4
  (row >>> (5 * (a * 14 + b))) &&& 31

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem profile_mono_even_finite : ∀ a b : Fin 15,
    a.val ≤ b.val → profile 0 a.val ≤ profile 0 b.val := by decide +kernel

theorem profile_mono_odd_finite : ∀ a b : Fin 14,
    a.val ≤ b.val → profile 1 a.val ≤ profile 1 b.val := by decide +kernel

theorem rank_adjacent_even : ∀ c : Fin 5, ∀ a : Fin 14, ∀ b : Fin 14,
    rank c a.val b.val ≤ rank c (a.val + 1) b.val := by decide +kernel

theorem rank_adjacent_odd : ∀ c : Fin 5, ∀ a : Fin 15, ∀ b : Fin 13,
    rank c a.val b.val ≤ rank c a.val (b.val + 1) := by decide +kernel

theorem rank_empty : ∀ c : Fin 5, rank c 0 0 = 0 := by decide +kernel
theorem rank_initial : ∀ c : Fin 5, rank c 14 13 = expected c := by decide +kernel

theorem full_budget_step : ∀ c : Fin 5, ∀ a : Fin 15, ∀ b : Fin 14,
    ∀ p : Fin (budget c + 1),
      rank c a.val b.val ≤ 1 + rank c
        (profile 1 (b.val - (budget c - p.val)))
        (profile 0 (a.val - p.val)) := by decide +kernel

theorem mono_from_adjacent (f : Nat → Nat) (cap : Nat)
    (h : ∀ k, k < cap → f k ≤ f (k + 1))
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ cap) : f a ≤ f b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b hab ih =>
      exact Nat.le_trans (ih (by omega)) (h b (by omega))

theorem rank_mono (c : Fin 5) (a b a' b' : Nat)
    (ha : a ≤ a') (hb : b ≤ b') (hacap : a' ≤ 14) (hbcap : b' ≤ 13) :
    rank c a b ≤ rank c a' b' := by
  have first : rank c a b ≤ rank c a' b := by
    apply mono_from_adjacent (fun k => rank c k b) 14 _ a a' ha hacap
    intro k hk
    exact rank_adjacent_even c ⟨k, hk⟩ ⟨b, by omega⟩
  have second : rank c a' b ≤ rank c a' b' := by
    apply mono_from_adjacent (fun k => rank c a' k) 13 _ b b' hb hbcap
    intro k hk
    exact rank_adjacent_odd c ⟨a', by omega⟩ ⟨k, hk⟩
  exact Nat.le_trans first second

theorem profile_mono_odd (a b : Nat) (hab : a ≤ b) (hb : b ≤ 13) :
    profile 1 a ≤ profile 1 b :=
  profile_mono_odd_finite ⟨a, by omega⟩ ⟨b, by omega⟩ hab

theorem profile_mono_even (a b : Nat) (hab : a ≤ b) (hb : b ≤ 14) :
    profile 0 a ≤ profile 0 b :=
  profile_mono_even_finite ⟨a, by omega⟩ ⟨b, by omega⟩ hab

/-- Any physical count transition above the isoperimetric bounds pays at most
one unit of the lower potential, with one unrestricted shared probe budget. -/
theorem physical_step (c : Fin 5) (a b a' b' p q : Nat)
    (ha : a ≤ 14) (hb : b ≤ 13) (ha' : a' ≤ 14) (hb' : b' ≤ 13)
    (shots : p + q ≤ budget c)
    (nextA : profile 1 (b - q) ≤ a')
    (nextB : profile 0 (a - p) ≤ b') :
    rank c a b ≤ 1 + rank c a' b' := by
  have hstep := full_budget_step c ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨p, by omega⟩
  have hq : q ≤ budget c - p := by omega
  have hmono := profile_mono_odd (b - (budget c - p)) (b - q) (by omega) (by omega)
  have hcompare := rank_mono c (profile 1 (b - (budget c - p)))
    (profile 0 (a - p)) a' b' (Nat.le_trans hmono nextA) nextB ha' hb'
  exact Nat.le_trans hstep (Nat.add_le_add_left hcompare 1)

end Princess.ThreeCubeTimeCounter

#print axioms Princess.ThreeCubeTimeCounter.physical_step
#print axioms Princess.ThreeCubeTimeCounter.rank_initial
