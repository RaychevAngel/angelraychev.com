import SixTypeObjective17Transfer
import SixTypeObjective17Delivery0
import SixTypeObjective17Delivery1
import SixTypeObjective17Delivery2
import SixTypeObjective17Delivery3
import SixTypeObjective17Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate17
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern17.pattern := by
  constructor
  · exact ⟨SixTypeObjective17Transfer.data, SixTypeObjective17Transfer.checked, SixTypeObjective17Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective17Delivery0.data, SixTypeObjective17Delivery0.checked, SixTypeObjective17Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective17Delivery1.data, SixTypeObjective17Delivery1.checked, SixTypeObjective17Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective17Delivery2.data, SixTypeObjective17Delivery2.checked, SixTypeObjective17Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective17Delivery3.data, SixTypeObjective17Delivery3.checked, SixTypeObjective17Delivery3.initial_states⟩
    · simp [SixTypePattern17.pattern] at present
    · exact ⟨SixTypeObjective17Delivery5.data, SixTypeObjective17Delivery5.checked, SixTypeObjective17Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate17
