import OddEndpointObjective021Transfer
import OddEndpointObjective021Delivery0
import OddEndpointObjective021Delivery1
import OddEndpointObjective021Delivery2
import OddEndpointObjective021Delivery3
import OddEndpointObjective021Delivery4
import OddEndpointObjective021Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate021
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern021
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective021Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective021Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective021Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective021Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective021Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective021Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective021Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate021
