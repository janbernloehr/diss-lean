import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # A global inverse is analytic when local inverse charts cover the source -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Local analytic inverses agree with any global right inverse of an
injective map, so the global inverse is analytic in the full target norm. -/
theorem analyticOnNhd_inverse_of_local_charts (f : E → F) (g : F → E)
    (hf : Function.Injective f) (hr : ∀ z, f (g z) = z)
    (hcharts : ∀ a, ∃ P : OpenPartialHomeomorph E F,
      (P : E → F) = f ∧ a ∈ P.source ∧ AnalyticOnNhd 𝕜 P.symm P.target) :
    AnalyticOnNhd 𝕜 g univ := by
  intro z _
  obtain ⟨P,hP,ha,hG⟩ := hcharts (g z)
  have hz : z ∈ P.target := by
    have h := P.map_source ha
    rwa [hP,hr] at h
  apply (hG z hz).congr
  filter_upwards [P.open_target.mem_nhds hz] with y hy
  apply hf
  have h : f (P.symm y) = y := by rw [← hP]; exact P.right_inv hy
  exact h.trans (hr y).symm

end NLS.ComplexAnalysis
