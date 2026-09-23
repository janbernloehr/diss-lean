import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints
import NLS.ZakharovShabat.PeriodOneEmbedding

/-!
# Common high-index periodic endpoint discs on the source space
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both canonical periodic endpoints lie in their free quarter-π disc on
one source neighborhood at every sufficiently distant index. -/
theorem exists_uniform_source_periodic_tail_isolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n := by
  let F : CoeffPair p → pairParitySubspace (p := p) 0 :=
    fun ψ => ⟨periodOnePotential ψ, periodOnePotential_mem ψ⟩
  have hF : Continuous F := by
    exact Continuous.subtype_mk (periodOnePotential (p := p)).continuous _
  obtain ⟨N, _, hlabel⟩ := exists_eventually_canonicalPeriodicEndpointLabeling hp hp1 (F φ)
  have hsource : ∀ᶠ ψ in 𝓝 φ, PeriodicEndpointLabeling hp (periodOnePotential ψ) N
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) := by
    simpa only [F] using hF.continuousAt.eventually hlabel
  obtain ⟨U, hUsub, hUopen, hφ⟩ := _root_.mem_nhds_iff.mp hsource
  refine ⟨N, U, hUopen, hφ, fun ψ hψ n hn => ?_⟩
  have hP := hUsub hψ
  exact ⟨(hP.distant n hn).left_mem, (hP.distant n hn).right_mem⟩

end NLS.ZakharovShabat
