import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient
import NLS.ZakharovShabat.SourceActionPoissonGradient

/-! # Commutation of the actual source discriminants and actions

The source cotangent coefficients at finite potentials are the physical
gradient coefficients at reversed frequencies. Bilinear Parseval therefore
identifies the actual source bracket with the physical cancellation. Finite
Fourier density and analytic continuity extend commutation to all sources
at every finite exponent at least two. The existing contour reduction then
proves the actual indexed action-action identity in Corollary 13.2.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual Hilbert source discriminants commute on finite Fourier
input, with the physical integral and Fourier sign proved explicitly. -/
theorem sourceBracket_discriminants_finite_eq_zero
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) w)
      (CoeffPair.ofFinsupp (p := 2) a) = 0 := by
  let L := sourceDiscriminantCotangent (by simp) z (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceDiscriminantCotangent (by simp) w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = 0
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceDiscriminant_finite_fst,
    cotangentCoefficients_sourceDiscriminant_finite_snd,neg_neg]
  have hz := continuous_classicalDiscriminantGradient (finiteSourceCurve a) z
  have hw := continuous_classicalDiscriminantGradient (finiteSourceCurve a) w
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,
    tsum_bilinear_unitFourierCoefficient hz.snd hw.fst]
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalDiscriminantGradient (finiteSourceCurve a) z s).1*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalDiscriminantGradient (finiteSourceCurve a) z s).2*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  change -I*(∫ s in (0 : ℝ)..1, classicalDiscriminantPairing (finiteSourceCurve a) z w s) = 0
  rw [integral_classicalDiscriminantPairing_eq_zero,mul_zero]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Source analyticity of a fixed spectral section of the actual discriminant. -/
theorem analyticOnNhd_sourceDiscriminant_section (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) univ := by
  intro ψ _
  exact (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).comp
    (f := fun χ : CoeffPair p => (z,χ)) (analyticAt_const.prod analyticAt_id)

/-- Actual discriminant commutation for every complex source at each
finite source exponent at least two. No finite or spectral identity is
left as a hypothesis. -/
theorem sourceBracket_discriminants_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : CoeffPair p) (z w : ℂ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ = 0 := by
  let F : ℂ → CoeffPair p → ℂ := fun t ψ => canonicalDiscriminant hp (periodOnePotential ψ) t
  have hF (t : ℂ) : AnalyticOnNhd ℂ (F t) univ := analyticOnNhd_sourceDiscriminant_section hp hp1 t
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      sourceBracket h2p (F z) (F w) (CoeffPair.ofFinsupp (p := p) a) = 0 := by
    have hrestrict (t : ℂ) : F t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential χ) t) := by
      funext χ
      exact (sourceDiscriminant_exponent (by simp) hp h2p χ t).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p (F z) (F w)
      (CoeffPair.ofFinsupp (p := 2) a)
      ((hF z _ (mem_univ _)).differentiableAt) ((hF w _ (mem_univ _)).differentiableAt)
    rw [hrestrict z,hrestrict w,CoeffPair.exponentInclusion_ofFinsupp,
      sourceBracket_discriminants_finite_eq_zero] at hc
    exact hc.symm
  have hcont : Continuous (sourceBracket h2p (F z) (F w)) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p (hF z) (hF w)).continuousOn
  have heq : sourceBracket h2p (F z) (F w) = (fun _ => (0 : ℂ)) :=
    (denseRange_finiteSourcePairs hp).equalizer hcont continuous_const (by
      funext a
      exact hfinite a)
  exact congrFun heq φ

/-- Corollary 13.2's action-action identity for the actual glued indexed
actions at every finite exponent at least two, including collapsed gaps. -/
theorem sourceBracket_actions_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ = 0 :=
  sourceBracket_actions_eq_zero_of_discriminant_commutes hp hp1 h2p φ hreal
    (fun z w => sourceBracket_discriminants_eq_zero hp hp1 h2p φ z w) n m

end NLS.ZakharovShabat
