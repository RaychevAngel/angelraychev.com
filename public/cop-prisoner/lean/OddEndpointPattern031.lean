import OddEndpointCertificatesSpec
import GroupedInitialMasks
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointPattern031
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
def residue : OddEndpointGraph.Case := 1
def patchAnchor : Option Int := some (6)
def frozenArena : Arena R C := arena residue patchAnchor
instance (x z : R) : Decidable (frozenArena.messenger x z) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).messenger x z))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).pursuer c d))
instance (x : R) (c : C) : Decidable (frozenArena.collision x c) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).collision x c))
theorem arena_eq : frozenArena=arena residue patchAnchor := rfl
def replyBits (r : Nat) : Nat := (if r < 45 then (if r < 22 then (if r < 11 then (if r < 5 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else (if r < 4 then 0 else 0))) else (if r < 8 then (if r < 6 then 0 else (if r < 7 then 1237940039285380274899124416 else 131456)) else (if r < 9 then 8960 else (if r < 10 then 1237940039285380274899125760 else 1237940039285380274899127296)))) else (if r < 16 then (if r < 13 then (if r < 12 then 22528 else 12352) else (if r < 14 then 8413184 else (if r < 15 then 573440 else 99328))) else (if r < 19 then (if r < 17 then 197120 else (if r < 18 then 1441792 else 790528)) else (if r < 20 then 538443776 else (if r < 21 then 36700160 else 6356992))))) else (if r < 33 then (if r < 27 then (if r < 24 then (if r < 23 then 12615680 else 92274688) else (if r < 25 then 50593792 else (if r < 26 then 34460401664 else 2348810240))) else (if r < 30 then (if r < 28 then 406847488 else (if r < 29 then 807403520 else 5905580032)) else (if r < 31 then 3238002688 else (if r < 32 then 2205465706496 else 150323855360)))) else (if r < 39 then (if r < 36 then (if r < 34 then 26038239232 else (if r < 35 then 51673825280 else 377957122048)) else (if r < 37 then 207232172032 else (if r < 38 then 141149805215744 else 9620726743040))) else (if r < 42 then (if r < 40 then 1666447310848 else (if r < 41 then 3307124817920 else 24189255811072)) else (if r < 43 then 13262859010048 else (if r < 44 then 9033587533807616 else 615726511554560)))))) else (if r < 68 then (if r < 56 then (if r < 50 then (if r < 47 then (if r < 46 then 106652627894272 else 211655988346880) else (if r < 48 then 1548112371908608 else (if r < 49 then 848822976643072 else 578149602163687424))) else (if r < 53 then (if r < 51 then 39406496739491840 else (if r < 52 then 6825768185233408 else 13545983254200320)) else (if r < 54 then 99079191802150912 else (if r < 55 then 54324670505156608 else 37001574538475995136)))) else (if r < 62 then (if r < 59 then (if r < 57 then 2522015791327477760 else (if r < 58 then 436849163854938112 else 866942928268820480)) else (if r < 60 then 6341068275337658368 else (if r < 61 then 3476778912330022912 else 2368100770462463688704))) else (if r < 65 then (if r < 63 then 161409010644958576640 else (if r < 64 then 27958346486716039168 else 55484347409204510720)) else (if r < 66 then 405828369621610135552 else (if r < 67 then 222513850389121466368 else 151558449309597676077056))))) else (if r < 79 then (if r < 73 then (if r < 70 then (if r < 69 then 10330176681277348904960 else 1789334175149826506752) else (if r < 71 then 3550998234189088686080 else (if r < 72 then 25973015655783048675328 else 14240886424903773847552))) else (if r < 76 then (if r < 74 then 9699740755814251268931584 else (if r < 75 then 661131307601750329917440 else 114517387209588896432128)) else (if r < 77 then 227263886988101675909120 else (if r < 78 then 1662273001970115115220992 else 911416731193841526243328)))) else (if r < 85 then (if r < 82 then (if r < 80 then 1239753428014802218661183488 else (if r < 81 then 1243984668383453420772655104 else 0)) else (if r < 83 then 14544888767238507258183680 else (if r < 84 then 1247611445842297308296773632 else 0))) else (if r < 88 then (if r < 86 then 0 else (if r < 87 then 0 else 0)) else (if r < 89 then 0 else (if r < 90 then 0 else 1254562769305081426051338176)))))))
def replyMasks (c : C) : Nat := replyBits c.val
def collisionBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 3 then 2475880078570760549798248447 else 2475880078570760549798248447)) else (if r < 6 then (if r < 5 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 7 then 262144 else 524288))) else (if r < 12 then (if r < 10 then (if r < 9 then 1048576 else 2097152) else (if r < 11 then 4194304 else 8388608)) else (if r < 14 then (if r < 13 then 16777216 else 33554432) else (if r < 15 then 67108864 else 134217728)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 268435456 else 536870912) else (if r < 19 then 1073741824 else 2147483648)) else (if r < 22 then (if r < 21 then 4294967296 else 8589934592) else (if r < 23 then 17179869184 else 34359738368))) else (if r < 28 then (if r < 26 then (if r < 25 then 68719476736 else 137438953472) else (if r < 27 then 274877906944 else 549755813888)) else (if r < 30 then (if r < 29 then 1099511627776 else 2199023255552) else (if r < 31 then 4398046511104 else (if r < 32 then 8796093022208 else 17592186044416)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 35184372088832 else 70368744177664) else (if r < 36 then 140737488355328 else 281474976710656)) else (if r < 39 then (if r < 38 then 562949953421312 else 1125899906842624) else (if r < 40 then 2251799813685248 else 4503599627370496))) else (if r < 45 then (if r < 43 then (if r < 42 then 9007199254740992 else 18014398509481984) else (if r < 44 then 36028797018963968 else 72057594037927936)) else (if r < 47 then (if r < 46 then 144115188075855872 else 288230376151711744) else (if r < 48 then 576460752303423488 else 1152921504606846976)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2305843009213693952 else 4611686018427387904) else (if r < 52 then 9223372036854775808 else 18446744073709551616)) else (if r < 55 then (if r < 54 then 36893488147419103232 else 73786976294838206464) else (if r < 56 then 147573952589676412928 else 295147905179352825856))) else (if r < 61 then (if r < 59 then (if r < 58 then 590295810358705651712 else 1180591620717411303424) else (if r < 60 then 2361183241434822606848 else 2475880078570760549798248447)) else (if r < 63 then (if r < 62 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 64 then 2475880078570760549798248447 else (if r < 65 then 2475880078570760549798248447 else 2475880078570760549798248447)))))))
def collisionMasks (x : R) : Nat := collisionBits x.val
def requiredBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else 0)) else (if r < 6 then (if r < 5 then 0 else 0) else (if r < 7 then 1254865000759985083344748480 else 1254865000759985083344486336))) else (if r < 12 then (if r < 10 then (if r < 9 then 1254865000759985083343962048 else 1254865000759985083342913472) else (if r < 11 then 1254865000759985083340816320 else 1254865000759985083336622016)) else (if r < 14 then (if r < 13 then 1254865000759985083328233408 else 1254865000759985083311456192) else (if r < 15 then 1254865000759985083277901760 else 1254865000759985083210792896)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 1254865000759985083076575168 else 1254865000759985082808139712) else (if r < 19 then 1254865000759985082271268800 else 1254865000759985081197526976)) else (if r < 22 then (if r < 21 then 1254865000759985079050043328 else 1254865000759985074755076032) else (if r < 23 then 1254865000759985066165141440 else 1254865000759985048985272256))) else (if r < 28 then (if r < 26 then (if r < 25 then 1254865000759985014625533888 else 1254865000759984945906057152) else (if r < 27 then 1254865000759984808467103680 else 1254865000759984533589196736)) else (if r < 30 then (if r < 29 then 1254865000759983983833382848 else 1254865000759982884321755072) else (if r < 31 then 1254865000759980685298499520 else (if r < 32 then 1254865000759976287251988416 else 1254865000759967491158966208)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 1254865000759949898972921792 else 1254865000759914714600832960) else (if r < 36 then 1254865000759844345856655296 else 1254865000759703608368299968)) else (if r < 39 then (if r < 38 then 1254865000759422133391589312 else 1254865000758859183438168000) else (if r < 40 then 1254865000757733283531325376 else 1254865000755481483717640128))) else (if r < 45 then (if r < 43 then (if r < 42 then 1254865000750977884090269632 else 1254865000741970684835528640) else (if r < 44 then 1254865000723956286326046656 else 1254865000687927489307082688)) else (if r < 47 then (if r < 46 then 1254865000615869895269154752 else 1254865000471754707193298880) else (if r < 48 then 1254865000183524331041587136 else 1254864999607063578738163648)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 1254864998454142074131316672 else 1254864996148299064917622720) else (if r < 52 then 1254864991536613046490234816 else 1254864982313241009635459008)) else (if r < 55 then (if r < 54 then 1254864963866496935925907392 else 1254864926973008788506804160) else (if r < 56 then 1254864853186032493668597696 else 1254864705612079903992184768))) else (if r < 61 then (if r < 59 then (if r < 58 then 1254864410464174724639358912 else 1254863820168364365933707200) else (if r < 60 then 1254862639576743648522403776 else 0)) else (if r < 63 then (if r < 62 then 0 else 0) else (if r < 64 then 0 else (if r < 65 then 0 else 0)))))))
def requiredMasks (x : R) : Nat := requiredBits x.val
def validMask : Nat := 1254865000759985083345010624
theorem reply_cases : ∀ c, presentC residue patchAnchor c →
    if c=outside then ∀ d, presentC residue patchAnchor d →
      (d=outside ∨ boundary residue d) → Has (replyMasks c) d
    else Has (replyMasks c) c ∧ ∀ b : Bool, permitted residue patchAnchor (cvertex c) b →
      Has (replyMasks c) (pack residue (next residue patchAnchor b (cvertex c))) := by
  unfold Has
  decide +kernel
theorem reply_coverage : ∀ c d, frozenArena.pursuer c d → Has (replyMasks c) d := by
  intro c d move
  obtain ⟨pc,pd,step⟩ := move
  have covered := reply_cases c pc
  by_cases out : c=outside
  · rw [if_pos out] at step covered
    exact covered d pd step
  · rw [if_neg out] at step covered
    rcases step with wait|⟨b,allowed,same⟩
    · simpa only [wait] using covered.1
    · rw [same]
      exact covered.2 b allowed
theorem collision_rows : ∀ x,
    (presentR residue patchAnchor x → Has (collisionMasks x) (pack residue (rvertex x))) ∧
    (¬presentR residue patchAnchor x → collisionMasks x=2^91-1) := by
  unfold Has
  decide +kernel
theorem collision_coverage : ∀ x c, frozenArena.collision x c → Has (collisionMasks x) c :=
  GroupedInitialMasks.collision_coverage (presentR residue patchAnchor)
    (fun x => pack residue (rvertex x)) collisionMasks collision_rows
theorem valid_bits : ∀ c, presentC residue patchAnchor c → Has validMask c := by
  unfold Has
  decide +kernel
theorem required_rows : ∀ x, presentR residue patchAnchor x →
    requiredMasks x=validMask ^^^ 2^(pack residue (rvertex x)).val := by
  decide +kernel
theorem required_coverage : ∀ x c, presentR residue patchAnchor x → presentC residue patchAnchor c →
    ¬(arena residue patchAnchor).collision x c → Has (requiredMasks x) c :=
  GroupedInitialMasks.required_coverage (presentR residue patchAnchor) (presentC residue patchAnchor)
    (fun x => pack residue (rvertex x)) validMask requiredMasks valid_bits required_rows
#print axioms arena_eq
#print axioms required_coverage
end Delivery.OddEndpointPattern031
