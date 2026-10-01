import NLS.ZakharovShabat.ClassicalSeparatedCommutation
import NLS.ZakharovShabat.SourceBoundaryRootPoisson

/-! # Actual separated source commutation and boundary-root involution

The physical same-boundary gradient cancellation and bilinear Parseval
prove commutation on finite Hilbert sources. Exponent restriction and
density extend it to all complex sources at finite exponents at least
two. The actual root cotangents then give mutual commutation within
each canonical Dirichlet or Neumann family at every real source.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Each actual Hilbert source separated characteristic family commutes on finite Fourier
input, with the physical integral and Fourier sign proved explicitly. -/
theorem sourceBracket_separated_finite_eq_zero
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ w)
      (CoeffPair.ofFinsupp (p := 2) a) = 0 := by
  let L := sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = 0
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceBoundaryCharacteristic_finite_fst,
    cotangentCoefficients_sourceBoundaryCharacteristic_finite_snd,neg_neg]
  have hz := continuous_classicalSeparatedGradient b (finiteSourceCurve a) z
  have hw := continuous_classicalSeparatedGradient b (finiteSourceCurve a) w
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,
    tsum_bilinear_unitFourierCoefficient hz.snd hw.fst]
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).1*
        (classicalSeparatedGradient b (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).2*
        (classicalSeparatedGradient b (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  change -I*(∫ s in (0 : ℝ)..1, classicalSeparatedPairing b (finiteSourceCurve a) z w s) = 0
  rw [integral_classicalSeparatedPairing_eq_zero,mul_zero]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each actual Dirichlet or Neumann characteristic family commutes at
all spectral parameters and every complex source at finite p at least two.
No finite identity, physical cancellation, or gradient is assumed. -/
theorem sourceBracket_separated_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z w : ℂ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ w) φ = 0 := by
  let F : ℂ → CoeffPair p → ℂ := fun t ψ => periodOneBoundaryCharacteristic hp hp1 b ψ t
  have hF (t : ℂ) : AnalyticOnNhd ℂ (F t) univ :=
    analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b t
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      sourceBracket h2p (F z) (F w) (CoeffPair.ofFinsupp (p := p) a) = 0 := by
    have hrestrict (t : ℂ) : F t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b χ t) := by
      funext χ
      exact (congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp
        (by norm_num) hp1 h2p b χ) t).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p (F z) (F w)
      (CoeffPair.ofFinsupp (p := 2) a)
      ((hF z _ (mem_univ _)).differentiableAt) ((hF w _ (mem_univ _)).differentiableAt)
    rw [hrestrict z,hrestrict w,CoeffPair.exponentInclusion_ofFinsupp,
      sourceBracket_separated_finite_eq_zero] at hc
    exact hc.symm
  have hcont : Continuous (sourceBracket h2p (F z) (F w)) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p (hF z) (hF w)).continuousOn
  have heq : sourceBracket h2p (F z) (F w) = (fun _ => (0 : ℂ)) :=
    (denseRange_finiteSourcePairs hp).equalizer hcont continuous_const (by
      funext a
      exact hfinite a)
  exact congrFun heq φ

/-- All actual canonical Dirichlet coordinates mutually commute, and
all actual canonical Neumann coordinates mutually commute. This includes
central indices and collapsed periodic gaps at every real source. -/
theorem sourceBracket_boundaryRoots_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) φ = 0 := by
  rw [sourceBracket_boundaryRoot_eq_characteristic hp hp1 h2p b φ hreal n,
    sourceBracket_antisymm,
    sourceBracket_boundaryRoot_eq_characteristic hp hp1 h2p b φ hreal m,
    sourceBracket_separated_eq_zero hp hp1 h2p b φ]
  simp

end NLS.ZakharovShabat
