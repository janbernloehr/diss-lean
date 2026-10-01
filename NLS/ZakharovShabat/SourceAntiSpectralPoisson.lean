import NLS.ZakharovShabat.ClassicalAntiSpectralPoisson
import NLS.ZakharovShabat.SourceAntiDiscriminantPoisson

/-! # Actual characteristic/anti-discriminant flow and anti commutation

The actual cotangent coefficients and bilinear Parseval identify the
finite Hilbert bracket with the physical endpoint cancellation. Analytic
continuity and exponent compatibility extend both results to every
complex source at finite exponents at least two.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

theorem sourceBracket_boundary_anti_finite_eq_physical
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ w)
      (CoeffPair.ofFinsupp (p := 2) a) =
        classicalGradientPoissonBracket (classicalSeparatedGradient b (finiteSourceCurve a) z)
          (classicalAntiDiscriminantGradient (finiteSourceCurve a) w) := by
  let L := sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceAntiDiscriminantCotangent (by simp) (by norm_num) w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = _
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceBoundaryCharacteristic_finite_fst,
    cotangentCoefficients_sourceBoundaryCharacteristic_finite_snd,
    cotangentCoefficients_sourceAntiDiscriminant_finite_fst,
    cotangentCoefficients_sourceAntiDiscriminant_finite_snd,neg_neg]
  have hz := continuous_classicalSeparatedGradient b (finiteSourceCurve a) z
  have hw := continuous_classicalAntiDiscriminantGradient (finiteSourceCurve a) w
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).1*
        (classicalAntiDiscriminantGradient (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).2*
        (classicalAntiDiscriminantGradient (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,tsum_bilinear_unitFourierCoefficient hz.snd hw.fst,
    ← intervalIntegral.integral_sub hi₁ hi₂]
  rfl

theorem sourceBracket_boundary_anti_finite
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    2*(z-w)*sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ w)
      (CoeffPair.ofFinsupp (p := 2) a) =
      extensionSign b*(periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) z*
        canonicalDiscriminant (by simp) (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) w-
        canonicalDiscriminant (by simp) (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) z*
          periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) w) := by
  rw [sourceBracket_boundary_anti_finite_eq_physical]
  simp only [periodOneBoundaryCharacteristic_finite_eq_classical,canonicalDiscriminant_finite_eq_classical]
  exact classicalGradientPoissonBracket_separated_anti_mul b (finiteSourceCurve a) z w

theorem sourceBracket_anti_anti_finite_eq_zero
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ w)
      (CoeffPair.ofFinsupp (p := 2) a) = 0 := by
  let L := sourceAntiDiscriminantCotangent (by simp) (by norm_num) z (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceAntiDiscriminantCotangent (by simp) (by norm_num) w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = _
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceAntiDiscriminant_finite_fst,
    cotangentCoefficients_sourceAntiDiscriminant_finite_snd,neg_neg]
  have hz := continuous_classicalAntiDiscriminantGradient (finiteSourceCurve a) z
  have hw := continuous_classicalAntiDiscriminantGradient (finiteSourceCurve a) w
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).1*
        (classicalAntiDiscriminantGradient (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).2*
        (classicalAntiDiscriminantGradient (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,tsum_bilinear_unitFourierCoefficient hz.snd hw.fst,
    ← intervalIntegral.integral_sub hi₁ hi₂]
  exact classicalGradientPoissonBracket_anti_eq_zero (finiteSourceCurve a) z w

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual signed characteristic/anti-discriminant flow at every
complex source, with its spectral difference cleared. -/
theorem sourceBracket_boundary_anti
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z w : ℂ) :
    2*(z-w)*sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w) φ =
      extensionSign b*(periodOneBoundaryCharacteristic hp hp1 b φ z*canonicalDiscriminant hp (periodOnePotential φ) w-
        canonicalDiscriminant hp (periodOnePotential φ) z*periodOneBoundaryCharacteristic hp hp1 b φ w) := by
  let C : ℂ → CoeffPair p → ℂ := fun t ψ => periodOneBoundaryCharacteristic hp hp1 b ψ t
  let A : ℂ → CoeffPair p → ℂ := fun t ψ => sourceAntiDiscriminantCandidate hp hp1 ψ t
  let D : ℂ → CoeffPair p → ℂ := fun t ψ => canonicalDiscriminant hp (periodOnePotential ψ) t
  have hC (t : ℂ) : AnalyticOnNhd ℂ (C t) univ := analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b t
  have hA (t : ℂ) : AnalyticOnNhd ℂ (A t) univ := analyticOnNhd_sourceAntiDiscriminant_section hp hp1 t
  have hD (t : ℂ) : AnalyticOnNhd ℂ (D t) univ := analyticOnNhd_sourceDiscriminant_section hp hp1 t
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      2*(z-w)*sourceBracket h2p (C z) (A w) (CoeffPair.ofFinsupp (p := p) a) =
        extensionSign b*(C z (CoeffPair.ofFinsupp (p := p) a)*D w (CoeffPair.ofFinsupp (p := p) a)-
          D z (CoeffPair.ofFinsupp (p := p) a)*C w (CoeffPair.ofFinsupp (p := p) a)) := by
    have hrestrictC (t : ℂ) : C t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b χ t) := by
      funext χ
      exact (congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p b χ) t).symm
    have hrestrictA (t : ℂ) : A t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) χ t) := by
      funext χ
      exact (congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp (by norm_num) hp1 h2p χ) t).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p (C z) (A w)
      (CoeffPair.ofFinsupp (p := 2) a) ((hC z _ (mem_univ _)).differentiableAt) ((hA w _ (mem_univ _)).differentiableAt)
    rw [hrestrictC z,hrestrictA w,CoeffPair.exponentInclusion_ofFinsupp] at hc
    rw [← hc]
    have hvalueC (t : ℂ) : C t (CoeffPair.ofFinsupp (p := p) a) =
        periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) t := by
      have h := congrFun (hrestrictC t) (CoeffPair.ofFinsupp (p := 2) a)
      simpa only [Function.comp_apply,CoeffPair.exponentInclusion_ofFinsupp] using h
    have hvalueD (t : ℂ) : D t (CoeffPair.ofFinsupp (p := p) a) =
        canonicalDiscriminant (by simp) (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) t := by
      have h := sourceDiscriminant_exponent (by simp) hp h2p (CoeffPair.ofFinsupp (p := 2) a) t
      rw [CoeffPair.exponentInclusion_ofFinsupp] at h
      exact h.symm
    rw [hvalueC z,hvalueC w,hvalueD z,hvalueD w]
    exact sourceBracket_boundary_anti_finite b a z w
  have hcC (t : ℂ) : Continuous (C t) := continuousOn_univ.mp (hC t).continuousOn
  have hcD (t : ℂ) : Continuous (D t) := continuousOn_univ.mp (hD t).continuousOn
  have hcB : Continuous (sourceBracket h2p (C z) (A w)) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p (hC z) (hA w)).continuousOn
  have heq : (fun ψ => 2*(z-w)*sourceBracket h2p (C z) (A w) ψ) =
      (fun ψ => extensionSign b*(C z ψ*D w ψ-D z ψ*C w ψ)) :=
    (denseRange_finiteSourcePairs hp).equalizer (continuous_const.mul hcB)
      (continuous_const.mul ((hcC z).mul (hcD w) |>.sub ((hcD z).mul (hcC w)))) (by
        funext a
        exact hfinite a)
  exact congrFun heq φ

/-- All actual anti-discriminants mutually commute on the whole complex
source space at finite exponents at least two. -/
theorem sourceBracket_anti_anti_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z w : ℂ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w) φ = 0 := by
  let A : ℂ → CoeffPair p → ℂ := fun t ψ => sourceAntiDiscriminantCandidate hp hp1 ψ t
  have hA (t : ℂ) : AnalyticOnNhd ℂ (A t) univ := analyticOnNhd_sourceAntiDiscriminant_section hp hp1 t
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      sourceBracket h2p (A z) (A w) (CoeffPair.ofFinsupp (p := p) a) = 0 := by
    have hrestrict (t : ℂ) : A t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) χ t) := by
      funext χ
      exact (congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp (by norm_num) hp1 h2p χ) t).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p (A z) (A w)
      (CoeffPair.ofFinsupp (p := 2) a) ((hA z _ (mem_univ _)).differentiableAt) ((hA w _ (mem_univ _)).differentiableAt)
    rw [hrestrict z,hrestrict w,CoeffPair.exponentInclusion_ofFinsupp,sourceBracket_anti_anti_finite_eq_zero] at hc
    exact hc.symm
  have hcont : Continuous (sourceBracket h2p (A z) (A w)) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p (hA z) (hA w)).continuousOn
  have heq : sourceBracket h2p (A z) (A w) = (fun _ => (0 : ℂ)) :=
    (denseRange_finiteSourcePairs hp).equalizer hcont continuous_const (by
      funext a
      exact hfinite a)
  exact congrFun heq φ

theorem analyticOnNhd_sourceBracket_boundary_anti_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w) φ) univ := by
  let L := sourceBivector h2p (sourceBoundaryCharacteristicCotangent hp hp1 b z φ)
  intro w _
  have hc := ((analyticOnNhd_sourceAntiDiscriminantCotangent_joint hp hp1) (w,φ) (mem_univ _)).comp
    (f := fun t : ℂ => (t,φ)) (analyticAt_id.prod analyticAt_const)
  exact (L.analyticAt _).comp hc

/-- The actual coincident characteristic/anti-discriminant bracket is
the signed characteristic/discriminant Wronskian, without singular division. -/
theorem sourceBracket_boundary_anti_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z) φ =
      extensionSign b*(canonicalDiscriminant hp (periodOnePotential φ) z*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z-
        periodOneBoundaryCharacteristic hp hp1 b φ z*deriv (canonicalDiscriminant hp (periodOnePotential φ)) z)/2 := by
  let B : ℂ → ℂ := fun w => sourceBracket h2p
    (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
    (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w) φ
  have hB : DifferentiableAt ℂ B z :=
    (analyticOnNhd_sourceBracket_boundary_anti_spectral hp hp1 h2p b φ z z (mem_univ _)).differentiableAt
  have hD := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) z (mem_univ _)).differentiableAt.hasDerivAt
  have hC := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ z (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun w : ℂ => 2*(z-w)*B w) =
      (fun w => extensionSign b*(periodOneBoundaryCharacteristic hp hp1 b φ z*canonicalDiscriminant hp (periodOnePotential φ) w-
        canonicalDiscriminant hp (periodOnePotential φ) z*periodOneBoundaryCharacteristic hp hp1 b φ w)) := by
    funext w
    exact sourceBracket_boundary_anti hp hp1 h2p b φ z w
  have hl := (((hasDerivAt_const z z).sub (hasDerivAt_id z)).const_mul (2 : ℂ)).mul hB.hasDerivAt
  change HasDerivAt (fun w : ℂ => 2*(z-w)*B w)
    (2*(0-1)*B z+2*(z-z)*deriv B z) z at hl
  have hr := ((hD.const_mul (periodOneBoundaryCharacteristic hp hp1 b φ z)).sub
    (hC.const_mul (canonicalDiscriminant hp (periodOnePotential φ) z))).const_mul (extensionSign b)
  rw [heq] at hl
  have hd := hl.unique hr
  simp only [sub_self,mul_zero,zero_mul,add_zero,zero_sub] at hd
  change B z = _
  linear_combination -(1/2 : ℂ)*hd

end NLS.ZakharovShabat
