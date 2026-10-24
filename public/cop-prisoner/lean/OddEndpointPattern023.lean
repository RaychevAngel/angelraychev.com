import OddEndpointCertificatesSpec
import GroupedInitialMasks
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointPattern023
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
def residue : OddEndpointGraph.Case := 1
def patchAnchor : Option Int := some (-2)
def frozenArena : Arena R C := arena residue patchAnchor
instance (x z : R) : Decidable (frozenArena.messenger x z) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).messenger x z))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).pursuer c d))
instance (x : R) (c : C) : Decidable (frozenArena.collision x c) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).collision x c))
theorem arena_eq : frozenArena=arena residue patchAnchor := rfl
def replyBits (r : Nat) : Nat := (if r < 45 then (if r < 22 then (if r < 11 then (if r < 5 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else (if r < 4 then 0 else 0))) else (if r < 8 then (if r < 6 then 0 else (if r < 7 then 1237940039285380274899124416 else 131456)) else (if r < 9 then 8960 else (if r < 10 then 1237940039285380274899125760 else 1237940039285380274899127296)))) else (if r < 16 then (if r < 13 then (if r < 12 then 22528 else 12352) else (if r < 14 then 8413184 else (if r < 15 then 573440 else 99328))) else (if r < 19 then (if r < 17 then 197120 else (if r < 18 then 1441792 else 790528)) else (if r < 20 then 538443776 else (if r < 21 then 36700160 else 6356992))))) else (if r < 33 then (if r < 27 then (if r < 24 then (if r < 23 then 12615680 else 92274688) else (if r < 25 then 50593792 else (if r < 26 then 34460401664 else 2348810240))) else (if r < 30 then (if r < 28 then 406847488 else (if r < 29 then 807403520 else 5905580032)) else (if r < 31 then 3238002688 else (if r < 32 then 2205465706496 else 158913789952)))) else (if r < 39 then (if r < 36 then (if r < 34 then 0 else (if r < 35 then 51673825280 else 377957122048)) else (if r < 37 then 207232172032 else (if r < 38 then 141149805215744 else 9620726743040))) else (if r < 42 then (if r < 40 then 1666447310848 else (if r < 41 then 3298534883328 else 24189255811072)) else (if r < 43 then 13262859010048 else (if r < 44 then 9033587533807616 else 615726511554560)))))) else (if r < 68 then (if r < 56 then (if r < 50 then (if r < 47 then (if r < 46 then 106652627894272 else 211655988346880) else (if r < 48 then 1548112371908608 else (if r < 49 then 848822976643072 else 578149602163687424))) else (if r < 53 then (if r < 51 then 39406496739491840 else (if r < 52 then 6825768185233408 else 13545983254200320)) else (if r < 54 then 99079191802150912 else (if r < 55 then 54324670505156608 else 37001574538475995136)))) else (if r < 62 then (if r < 59 then (if r < 57 then 2522015791327477760 else (if r < 58 then 436849163854938112 else 866942928268820480)) else (if r < 60 then 6341068275337658368 else (if r < 61 then 3476778912330022912 else 2368100770462463688704))) else (if r < 65 then (if r < 63 then 161409010644958576640 else (if r < 64 then 27958346486716039168 else 55484347409204510720)) else (if r < 66 then 405828369621610135552 else (if r < 67 then 222513850389121466368 else 151558449309597676077056))))) else (if r < 79 then (if r < 73 then (if r < 70 then (if r < 69 then 10330176681277348904960 else 1789334175149826506752) else (if r < 71 then 3550998234189088686080 else (if r < 72 then 25973015655783048675328 else 14240886424903773847552))) else (if r < 76 then (if r < 74 then 9699740755814251268931584 else (if r < 75 then 661131307601750329917440 else 114517387209588896432128)) else (if r < 77 then 227263886988101675909120 else (if r < 78 then 1662273001970115115220992 else 911416731193841526243328)))) else (if r < 85 then (if r < 82 then (if r < 80 then 1239753428014802218661183488 else (if r < 81 then 1241566816744224162423242752 else 7329112781413689371656192)) else (if r < 83 then 14544888767238507258183680 else (if r < 84 then 1247611445842297308296773632 else 0))) else (if r < 88 then (if r < 86 then 0 else (if r < 87 then 0 else 0)) else (if r < 89 then 0 else (if r < 90 then 0 else 1256980620944310684400750528)))))))
def replyMasks (c : C) : Nat := replyBits c.val
def collisionBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 3 then 2475880078570760549798248447 else 2475880078570760549798248447)) else (if r < 6 then (if r < 5 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 7 then 262144 else 524288))) else (if r < 12 then (if r < 10 then (if r < 9 then 1048576 else 2097152) else (if r < 11 then 4194304 else 8388608)) else (if r < 14 then (if r < 13 then 16777216 else 33554432) else (if r < 15 then 67108864 else 134217728)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 268435456 else 536870912) else (if r < 19 then 1073741824 else 2147483648)) else (if r < 22 then (if r < 21 then 4294967296 else 2475880078570760549798248447) else (if r < 23 then 17179869184 else 34359738368))) else (if r < 28 then (if r < 26 then (if r < 25 then 68719476736 else 137438953472) else (if r < 27 then 274877906944 else 549755813888)) else (if r < 30 then (if r < 29 then 1099511627776 else 2199023255552) else (if r < 31 then 4398046511104 else (if r < 32 then 8796093022208 else 17592186044416)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 35184372088832 else 70368744177664) else (if r < 36 then 140737488355328 else 281474976710656)) else (if r < 39 then (if r < 38 then 562949953421312 else 1125899906842624) else (if r < 40 then 2251799813685248 else 4503599627370496))) else (if r < 45 then (if r < 43 then (if r < 42 then 9007199254740992 else 18014398509481984) else (if r < 44 then 36028797018963968 else 72057594037927936)) else (if r < 47 then (if r < 46 then 144115188075855872 else 288230376151711744) else (if r < 48 then 576460752303423488 else 1152921504606846976)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2305843009213693952 else 4611686018427387904) else (if r < 52 then 9223372036854775808 else 18446744073709551616)) else (if r < 55 then (if r < 54 then 36893488147419103232 else 73786976294838206464) else (if r < 56 then 147573952589676412928 else 295147905179352825856))) else (if r < 61 then (if r < 59 then (if r < 58 then 590295810358705651712 else 1180591620717411303424) else (if r < 60 then 2361183241434822606848 else 2475880078570760549798248447)) else (if r < 63 then (if r < 62 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 64 then 2475880078570760549798248447 else (if r < 65 then 2475880078570760549798248447 else 2475880078570760549798248447)))))))
def collisionMasks (x : R) : Nat := collisionBits x.val
def requiredBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else 0)) else (if r < 6 then (if r < 5 then 0 else 0) else (if r < 7 then 1257282852399214333104226240 else 1257282852399214333103964096))) else (if r < 12 then (if r < 10 then (if r < 9 then 1257282852399214333103439808 else 1257282852399214333102391232) else (if r < 11 then 1257282852399214333100294080 else 1257282852399214333096099776)) else (if r < 14 then (if r < 13 then 1257282852399214333087711168 else 1257282852399214333070933952) else (if r < 15 then 1257282852399214333037379520 else 1257282852399214332970270656)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 1257282852399214332836052928 else 1257282852399214332567617472) else (if r < 19 then 1257282852399214332030746560 else 1257282852399214330957004736)) else (if r < 22 then (if r < 21 then 1257282852399214328809521088 else 0) else (if r < 23 then 1257282852399214315924619200 else 1257282852399214298744750016))) else (if r < 28 then (if r < 26 then (if r < 25 then 1257282852399214264385011648 else 1257282852399214195665534912) else (if r < 27 then 1257282852399214058226581440 else 1257282852399213783348674496)) else (if r < 30 then (if r < 29 then 1257282852399213233592860608 else 1257282852399212134081232832) else (if r < 31 then 1257282852399209935057977280 else (if r < 32 then 1257282852399205537011466176 else 1257282852399196740918443968)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 1257282852399179148732399552 else 1257282852399143964360310720) else (if r < 36 then 1257282852399073595616133056 else 1257282852398932858127777728)) else (if r < 39 then (if r < 38 then 1257282852398651383151067072 else 1257282852398088433197645760) else (if r < 40 then 1257282852396962533290803136 else 1257282852394710733477117888))) else (if r < 45 then (if r < 43 then (if r < 42 then 1257282852390207133849747392 else 1257282852381199934595006400) else (if r < 44 then 1257282852363185536085524416 else 1257282852327156739066560448)) else (if r < 47 then (if r < 46 then 1257282852255099145028632512 else 1257282852110983956952776640) else (if r < 48 then 1257282851822753580801064896 else 1257282851246292828497641408)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 1257282850093371323890794432 else 1257282847787528314677100480) else (if r < 52 then 1257282843175842296249712576 else 1257282833952470259394936768)) else (if r < 55 then (if r < 54 then 1257282815505726185685385152 else 1257282778612238038266281920) else (if r < 56 then 1257282704825261743428075456 else 1257282557251309153751662528))) else (if r < 61 then (if r < 59 then (if r < 58 then 1257282262103403974398836672 else 1257281671807593615693184960) else (if r < 60 then 1257280491215972898281881536 else 0)) else (if r < 63 then (if r < 62 then 0 else 0) else (if r < 64 then 0 else (if r < 65 then 0 else 0)))))))
def requiredMasks (x : R) : Nat := requiredBits x.val
def validMask : Nat := 1257282852399214333104488384
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
end Delivery.OddEndpointPattern023
