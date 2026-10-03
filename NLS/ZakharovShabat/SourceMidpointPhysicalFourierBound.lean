import NLS.ZakharovShabat.ContinuousSourceDiscriminantGradient
import NLS.ZakharovShabat.SourceMidpointGradientOperatorContour
import NLS.ZakharovShabat.ClassicalContourGradientIntegrandBound
import NLS.SequenceSpaces.SourceCotangentNormBound

/-! # Physical Fourier bounds for the actual midpoint operator integrand

Unconjugated source duality reverses frequencies, an isometry of the
conjugate coefficient space. The two physical component Fourier norms
therefore bound the actual source operator integrand in G.7.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The actual source contour operator is bounded by its two physical
conjugate Fourier norms at every continuously represented Hilbert source
included into a finite source exponent at least two. -/
theorem norm_sourceMidpointContourIntegrand_le_physical_fourier
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (hq : 1 < q)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    ‖sourceMidpointContourIntegrand hp (CoeffPair.exponentInclusion h2p φ) z‖ ≤
      ‖classicalDiscriminantQuotientGradientFourierCoefficients hq Φ z (ContinuousLinearMap.fst ℝ ℂ ℂ)‖+
      ‖classicalDiscriminantQuotientGradientFourierCoefficients hq Φ z (ContinuousLinearMap.snd ℝ ℂ ℂ)‖ := by
  let a := classicalDiscriminantQuotientGradientFourierCoefficients hq Φ z (ContinuousLinearMap.fst ℝ ℂ ℂ)
  let b := classicalDiscriminantQuotientGradientFourierCoefficients hq Φ z (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hΔ : canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z =
      classicalDiscriminant Φ z :=
    (sourceDiscriminant_exponent (by simp) hp h2p φ z).symm.trans
      (canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) Φ hΦ z)
  have hcoeff (f : ℝ → ℂ) (n : ℤ) :
      intervalFourierCoefficient 1 f n = unitFourierCoefficient f n := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  have hleft (n : ℤ) : sourceMidpointContourIntegrand hp (CoeffPair.exponentInclusion h2p φ) z
      (CoeffPair.inlCLM (lp.single p n 1)) = Coeff.reflection a n := by
    change (canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z/
      ((canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z)^2-4))*
      sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ)
        (CoeffPair.inlCLM (lp.single p n 1)) = _
    rw [hΔ,sourceDiscriminantCotangent_continuous_single_fst hp hp1 h2p φ Φ hΦ z n]
    simp only [Coeff.reflection_apply,a,classicalDiscriminantQuotientGradientFourierCoefficients_apply]
    rw [intervalFourierCoefficient_const_mul,hcoeff]
    rfl
  have hright (n : ℤ) : sourceMidpointContourIntegrand hp (CoeffPair.exponentInclusion h2p φ) z
      (CoeffPair.inrCLM (lp.single p n 1)) = Coeff.reflection b n := by
    change (canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z/
      ((canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z)^2-4))*
      sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ)
        (CoeffPair.inrCLM (lp.single p n 1)) = _
    rw [hΔ,sourceDiscriminantCotangent_continuous_single_snd hp hp1 h2p φ Φ hΦ z n]
    simp only [Coeff.reflection_apply,b,classicalDiscriminantQuotientGradientFourierCoefficients_apply]
    rw [intervalFourierCoefficient_const_mul,hcoeff]
    rfl
  simpa only [LinearIsometryEquiv.norm_map] using
    CoeffPair.norm_cotangent_le_of_single hp _ (Coeff.reflection a) (Coeff.reflection b) hleft hright

/-- One physical H¹ ball supplies one outer summable bound for the actual
source operator integrand at every distant contour point. The compatibility
premise identifies the represented potential, not its derivative. -/
theorem exists_sourceMidpointContourIntegrand_sobolev_uniform_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (s : ℝ) (hs : 1 < s) (hq : ENNReal.ofReal (1+1/s) < q) (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal s) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M → ∀ φ : CoeffPair 2,
      physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)]
        extend (classicalSobolevPotential a) →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4),
        ‖sourceMidpointContourIntegrand hp (CoeffPair.exponentInclusion h2p φ) z‖ ≤ b n := by
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  obtain ⟨N,hN,b,hb,h⟩ := exists_classicalContourGradientIntegrand_uniform_memlp s hs q hq M hM
    (Real.pi/4) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨N,hN,fun n => 2*b n,hb.const_mul 2,?_⟩
  intro a ha φ hΦ n hn z hz
  have h₁ := (h a ha (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..) n hn z hz).2
  have h₂ := (h a ha (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..) n hn z hz).2
  exact (norm_sourceMidpointContourIntegrand_le_physical_fourier hp hp1 h2p hq1 φ _ hΦ z).trans
    (by linarith)

end NLS.ZakharovShabat
