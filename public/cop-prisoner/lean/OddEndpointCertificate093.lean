import OddEndpointObjective093Transfer
import OddEndpointObjective093Delivery0
import OddEndpointObjective093Delivery1
import OddEndpointObjective093Delivery2
import OddEndpointObjective093Delivery3
import OddEndpointObjective093Delivery4
import OddEndpointObjective093Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate093
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern093
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective093Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective093Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective093Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective093Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective093Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective093Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective093Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate093
