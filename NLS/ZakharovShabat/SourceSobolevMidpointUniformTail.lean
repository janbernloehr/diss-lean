import NLS.ZakharovShabat.SourceMidpointSequenceAnalytic
import NLS.ZakharovShabat.NormalizedSobolevSourceCompact
import NLS.SequenceSpaces.CompactPullbackCoordinateTails

/-! Actual midpoint displacements have uniform tails on one fixed
full complex normalized Sobolev neighborhood at every positive order. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem exists_local_sobolev_midpoint_uniform_tail
    (hp : p≠⊤) (hp1 : 1<p) (t : ℝ) (ht : 0<t)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ∈T ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ k : ℤ, K≤k.natAbs →
        ‖sourcePeriodicMidpointDisplacement hp hp1
          (normalizedWeightedSource (sourceSobolevSpectralWeight t ht.le) ψ) k‖≤ε := by
  let w := sourceSobolevSpectralWeight t ht.le
  let L := normalizedWeightedSourceCLM (p := p) w
  obtain ⟨V,hV,hrealV,ha⟩ := exists_sourcePeriodicMidpointDisplacement_analytic_common_domain hp hp1
  obtain ⟨T,hT,hφT,_,htail⟩ := Coeff.exists_local_uniform_coordinate_tails_compact_pullback hp L
    (isCompactOperator_normalizedSobolevSource t ht) (sourcePeriodicMidpointDisplacement hp hp1)
    hV ha.continuousOn φ (hrealV (normalizedWeightedSource_realType w φ hφ))
  exact ⟨T,hT,hφT,fun ε hε => by
    obtain ⟨K,hK⟩ := htail ε hε
    exact ⟨K,fun ψ hψ k hk => (hK ψ hψ k hk).le⟩⟩

end NLS.ZakharovShabat
