import NLS.ZakharovShabat.SourceFloquetExteriorCircleBound
import NLS.ZakharovShabat.SourceFiniteGapExterior
import NLS.ComplexAnalysis.ExteriorCircleBounds
import NLS.ComplexAnalysis.ExteriorRemovableSingularity

/-! # Removability at infinity of the finite-gap logarithmic derivative

Free asymptotics bound the quotient on escaping circles. Maximum modulus
fills all exterior annuli, and inversion turns the resulting exterior
bound into a removable singularity at zero.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual finite-gap logarithmic derivative is bounded throughout a
full exterior region, including all collapsed spectral points there. -/
theorem exists_sourceFiniteGap_logDerivative_exterior_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R M : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ (sourceFloquetLogDerivative hp hp1 φ.val) {z : ℂ | R < ‖z‖} ∧
      ∀ z : ℂ, R < ‖z‖ → ‖sourceFloquetLogDerivative hp hp1 φ.val z‖ ≤ M := by
  obtain ⟨A, hA, _, _, _, ha⟩ := exists_sourceFiniteGap_analytic_exterior hp hp1 φ hf
  obtain ⟨R, M, hR, hb⟩ := exists_exterior_bound_of_escaping_circle_bounds
    (sourceFloquetLogDerivative hp hp1 φ.val) A ha centralCircleRadius
    tendsto_centralCircleRadius_atTop 4
    (eventually_centralCircle_sourceFloquetLogDerivative_bound hp hp1 φ.val φ.property)
  refine ⟨max A R, M, hA.trans_le (le_max_left _ _), ?_, ?_⟩
  · apply ha.mono
    intro z hz
    exact lt_of_le_of_lt (le_max_left A R) hz
  · intro z hz
    exact hb z (lt_of_le_of_lt (le_max_right _ _) hz)

/-- The inverted actual finite-gap logarithmic derivative has an analytic
extension across zero. This discharges the removable-singularity input
needed for a convergent expansion at infinity. -/
theorem exists_sourceFiniteGap_logDerivative_analytic_at_infinity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ.val z⁻¹ := by
  obtain ⟨R, M, hR, ha, hb⟩ := exists_sourceFiniteGap_logDerivative_exterior_bound hp hp1 φ hf
  obtain ⟨g, hg, he⟩ := exists_analytic_inversion_extension_of_exterior_bound
    (sourceFloquetLogDerivative hp hp1 φ.val) R M hR ha hb
  exact ⟨R⁻¹, inv_pos.mpr hR, g, hg, he⟩

/-- Every analytic inversion extension has the canonical free value at zero. -/
theorem sourceFloquetLogDerivative_inversionExtension_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (r : ℝ) (hr : 0 < r)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (he : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ z⁻¹) :
    g 0 = -I := by
  let z : ℕ → ℂ := fun k => (centralCircleRadius k : ℂ)
  have hnorm (k : ℕ) : ‖z k‖ = centralCircleRadius k := by
    simp only [z, norm_real, Real.norm_eq_abs, abs_of_pos (centralCircleRadius_pos k)]
  have hescape : Tendsto (fun k => ‖z k‖) atTop atTop := by
    simpa only [hnorm] using tendsto_centralCircleRadius_atTop
  have hz0 (k : ℕ) : z k ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact centralCircleRadius_pos k)
  have hsep (k : ℕ) (n : ℤ) : Real.pi/4 ≤ ‖z k-(Real.pi : ℂ)*n‖ := by
    have hs : z k ∈ sphere (0 : ℂ) (centralCircleRadius k) := by
      simpa only [mem_sphere, dist_zero_right] using hnorm k
    have h := centralCircle_lattice_gap k hs n
    nlinarith [Real.pi_pos]
  have hq := tendsto_sourceFloquetLogDerivative_of_separated hp hp1 φ hφ z hescape
    (by positivity : 0 < Real.pi/4) le_rfl hsep
  have hi : Tendsto (fun k => (z k)⁻¹) atTop (𝓝 (0 : ℂ)) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hescape)
  have hG := hg.continuousAt.tendsto.comp hi
  have hG' : Tendsto (fun k => sourceFloquetLogDerivative hp hp1 φ (z k)) atTop (𝓝 (g 0)) := by
    apply hG.congr'
    filter_upwards [hi.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))] with k hk
    dsimp only [Function.comp_def]
    rw [he ((z k)⁻¹) hk (inv_ne_zero (hz0 k)), inv_inv]
  exact tendsto_nhds_unique hG' hq

/-- The analytic germ at infinity has the exact canonical leading value `-i`. -/
theorem exists_sourceFiniteGap_logDerivative_normalized_at_infinity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r) ∧ g 0 = -I ∧
      ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ.val z⁻¹ := by
  obtain ⟨r, hr, g, hg, he⟩ := exists_sourceFiniteGap_logDerivative_analytic_at_infinity hp hp1 φ hf
  exact ⟨r, hr, g, hg, sourceFloquetLogDerivative_inversionExtension_zero hp hp1 φ.val φ.property
    r hr g (hg 0 (mem_ball_self hr)) he, he⟩

end NLS.ZakharovShabat
