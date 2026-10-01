import NLS.ZakharovShabat.SourceAntiDiscriminantPoissonGradient
import NLS.ZakharovShabat.SourceBoundaryDiscriminantPoisson

/-! # Actual anti-discriminant/discriminant source flow

The actual anti-discriminant cotangent and bilinear Parseval identify
the finite source bracket with the proved physical Hamiltonian variation.
Exponent restriction and density extend the characteristic determinant
formula to every complex source at finite exponents at least two.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At a finite source the actual Poisson bracket equals the actual physical
anti-discriminant derivative, with the Fourier reversal and Poisson sign proved. -/
theorem sourceBracket_anti_discriminant_finite_eq_physical
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) w)
      (CoeffPair.ofFinsupp (p := 2) a) =
        (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z)
          (finiteSourceCurve a)) (classicalDiscriminantHamiltonianDirection (finiteSourceCurve a) w) := by
  let L := sourceAntiDiscriminantCotangent (by simp) (by norm_num) z
    (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceDiscriminantCotangent (by simp) w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = _
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceAntiDiscriminant_finite_fst,
    cotangentCoefficients_sourceAntiDiscriminant_finite_snd,
    cotangentCoefficients_sourceDiscriminant_finite_fst,
    cotangentCoefficients_sourceDiscriminant_finite_snd,neg_neg]
  have hz := continuous_classicalAntiDiscriminantGradient (finiteSourceCurve a) z
  have hw := continuous_classicalDiscriminantGradient (finiteSourceCurve a) w
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,
    tsum_bilinear_unitFourierCoefficient hz.snd hw.fst]
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).1*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).2*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hi₁ hi₂,← intervalIntegral.integral_const_mul,
    fderiv_classicalAntiDiscriminant_eq_gradient_integral]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
    classicalDiscriminantHamiltonianDirection,ContinuousMap.coe_mk]
  ring


/-- The actual finite Hilbert anti-discriminant/discriminant source bracket
is the determinant of the original normalized separated characteristics. -/
theorem sourceBracket_anti_discriminant_finite
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    (z-w)*sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) w)
      (CoeffPair.ofFinsupp (p := 2) a) =
        periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet (CoeffPair.ofFinsupp (p := 2) a) z*
          periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann (CoeffPair.ofFinsupp (p := 2) a) w-
        periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann (CoeffPair.ofFinsupp (p := 2) a) z*
          periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet (CoeffPair.ofFinsupp (p := 2) a) w := by
  rw [sourceBracket_anti_discriminant_finite_eq_physical]
  simp only [periodOneBoundaryCharacteristic_finite_eq_classical]
  exact fderiv_classicalAntiDiscriminant_hamiltonian (finiteSourceCurve a) z w

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed spectral section of the actual source anti-discriminant is entire. -/
theorem analyticOnNhd_sourceAntiDiscriminant_section
    (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z) univ := by
  intro ψ _
  exact (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (z,ψ) (mem_univ _)).comp
    (f := fun χ : CoeffPair p => (z,χ)) (analyticAt_const.prod analyticAt_id)

/-- The actual source anti-discriminant/discriminant bracket holds for every
complex source, including coincident parameters, at each finite p at least two. -/
theorem sourceBracket_anti_discriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z w : ℂ) :
    (z-w)*sourceBracket h2p
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
          periodOneBoundaryCharacteristic hp hp1 .neumann φ z*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w := by
  let F : CoeffPair p → ℂ := fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ z
  let G : CoeffPair p → ℂ := fun ψ => canonicalDiscriminant hp (periodOnePotential ψ) w
  let C : BoundaryCondition → ℂ → CoeffPair p → ℂ := fun b t ψ => periodOneBoundaryCharacteristic hp hp1 b ψ t
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_sourceAntiDiscriminant_section hp hp1 z
  have hG : AnalyticOnNhd ℂ G univ := analyticOnNhd_sourceDiscriminant_section hp hp1 w
  have hC (b : BoundaryCondition) (t : ℂ) : AnalyticOnNhd ℂ (C b t) univ :=
    analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b t
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      (z-w)*sourceBracket h2p F G (CoeffPair.ofFinsupp (p := p) a) =
        C .dirichlet z (CoeffPair.ofFinsupp (p := p) a)*C .neumann w (CoeffPair.ofFinsupp (p := p) a)-
          C .neumann z (CoeffPair.ofFinsupp (p := p) a)*C .dirichlet w (CoeffPair.ofFinsupp (p := p) a) := by
    have hrestrictF : F ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) χ z) := by
      funext χ
      exact (congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp (by norm_num) hp1 h2p χ) z).symm
    have hrestrictG : G ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential χ) w) := by
      funext χ
      exact (sourceDiscriminant_exponent (by simp) hp h2p χ w).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p F G
      (CoeffPair.ofFinsupp (p := 2) a) ((hF _ (mem_univ _)).differentiableAt) ((hG _ (mem_univ _)).differentiableAt)
    rw [hrestrictF,hrestrictG,CoeffPair.exponentInclusion_ofFinsupp] at hc
    rw [← hc]
    have hvalueC (b : BoundaryCondition) (t : ℂ) : C b t (CoeffPair.ofFinsupp (p := p) a) =
        periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) t := by
      have h := congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p b
        (CoeffPair.ofFinsupp (p := 2) a)) t
      rw [CoeffPair.exponentInclusion_ofFinsupp] at h
      exact h.symm
    rw [hvalueC .dirichlet z,hvalueC .neumann w,hvalueC .neumann z,hvalueC .dirichlet w]
    exact sourceBracket_anti_discriminant_finite a z w
  have hcC (b : BoundaryCondition) (t : ℂ) : Continuous (C b t) := continuousOn_univ.mp (hC b t).continuousOn
  have hcB : Continuous (sourceBracket h2p F G) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p hF hG).continuousOn
  have heq : (fun ψ => (z-w)*sourceBracket h2p F G ψ) =
      (fun ψ => C .dirichlet z ψ*C .neumann w ψ-C .neumann z ψ*C .dirichlet w ψ) :=
    (denseRange_finiteSourcePairs hp).equalizer (continuous_const.mul hcB)
      (((hcC .dirichlet z).mul (hcC .neumann w)).sub ((hcC .neumann z).mul (hcC .dirichlet w))) (by
        funext a
        exact hfinite a)
  exact congrFun heq φ

/-- Distinct parameters recover the literal characteristic determinant quotient. -/
theorem sourceBracket_anti_discriminant_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z w : ℂ) (hzw : z ≠ w) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
          periodOneBoundaryCharacteristic hp hp1 .neumann φ z*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w)/(z-w) := by
  apply (eq_div_iff (sub_ne_zero.mpr hzw)).mpr
  rw [mul_comm]
  exact sourceBracket_anti_discriminant hp hp1 h2p φ z w

/-- The actual fixed-source bracket is entire in the discriminant spectral
parameter, by the analytic operator-valued discriminant differential. -/
theorem analyticOnNhd_sourceBracket_anti_discriminant_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => sourceBracket h2p
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) univ := by
  let L := sourceBivector h2p (sourceAntiDiscriminantCotangent hp hp1 z φ)
  intro w _
  have hc := ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1) (w,φ) (mem_univ _)).comp
    (f := fun t : ℂ => (t,φ)) (analyticAt_id.prod analyticAt_const)
  exact (L.analyticAt _).comp hc

/-- The entire source bracket resolves the coincident-parameter quotient
to the literal Wronskian of the two original separated characteristics. -/
theorem sourceBracket_anti_discriminant_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceBracket h2p
      (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ =
        periodOneBoundaryCharacteristic hp hp1 .neumann φ z*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) z-
          periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*deriv (periodOneBoundaryCharacteristic hp hp1 .neumann φ) z := by
  let B : ℂ → ℂ := fun w => sourceBracket h2p
    (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ
  have hB : DifferentiableAt ℂ B z :=
    (analyticOnNhd_sourceBracket_anti_discriminant_spectral hp hp1 h2p φ z z (mem_univ _)).differentiableAt
  have hD := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hN := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .neumann φ z (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun w : ℂ => (z-w)*B w) =
      (fun w => periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
        periodOneBoundaryCharacteristic hp hp1 .neumann φ z*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w) := by
    funext w
    exact sourceBracket_anti_discriminant hp hp1 h2p φ z w
  have hleft := ((hasDerivAt_const z z).sub (hasDerivAt_id z)).mul hB.hasDerivAt
  change HasDerivAt (fun w : ℂ => (z-w)*B w) ((0-1)*B z+(z-z)*deriv B z) z at hleft
  have hright := (hN.const_mul (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z)).sub
    (hD.const_mul (periodOneBoundaryCharacteristic hp hp1 .neumann φ z))
  rw [heq] at hleft
  have hd := hleft.unique hright
  simp only [sub_self,zero_mul,add_zero,zero_sub,neg_one_mul] at hd
  change B z = _
  linear_combination -hd

end NLS.ZakharovShabat
