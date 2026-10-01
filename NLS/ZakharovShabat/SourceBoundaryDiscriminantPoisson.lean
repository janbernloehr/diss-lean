import NLS.ZakharovShabat.SourceBoundaryPoissonGradient
import NLS.ZakharovShabat.SourceDiscriminantPoisson

/-! # Actual separated-characteristic/discriminant source brackets

Bilinear Parseval identifies the actual finite source bracket with the
physical characteristic variation along the discriminant Hamiltonian.
The proved monodromy commutator therefore gives the original signed
characteristic/anti-discriminant formula. Exponent restriction and density
extend it to every complex source at each finite exponent at least two.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- At a finite source the actual Poisson bracket equals the actual physical
characteristic derivative, with the Fourier reversal and Poisson sign proved. -/
theorem sourceBracket_boundary_discriminant_finite_eq_physical
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) w)
      (CoeffPair.ofFinsupp (p := 2) a) =
        (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z)
          (finiteSourceCurve a)) (classicalDiscriminantHamiltonianDirection (finiteSourceCurve a) w) := by
  let L := sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z
    (CoeffPair.ofFinsupp (p := 2) a)
  let M := sourceDiscriminantCotangent (by simp) w (CoeffPair.ofFinsupp (p := 2) a)
  change hilbertPairBivector (CoeffPair.cotangentCoefficients (by norm_num) L)
    (CoeffPair.cotangentCoefficients (by norm_num) M) = _
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  simp only [L,M,cotangentCoefficients_sourceBoundaryCharacteristic_finite_fst,
    cotangentCoefficients_sourceBoundaryCharacteristic_finite_snd,
    cotangentCoefficients_sourceDiscriminant_finite_fst,
    cotangentCoefficients_sourceDiscriminant_finite_snd,neg_neg]
  have hz := continuous_classicalSeparatedGradient b (finiteSourceCurve a) z
  have hw := continuous_classicalDiscriminantGradient (finiteSourceCurve a) w
  rw [tsum_bilinear_unitFourierCoefficient hz.fst hw.snd,
    tsum_bilinear_unitFourierCoefficient hz.snd hw.fst]
  have hi₁ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).1*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).2) volume 0 1 :=
    (hz.fst.mul hw.snd).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ =>
      (classicalSeparatedGradient b (finiteSourceCurve a) z s).2*
        (classicalDiscriminantGradient (finiteSourceCurve a) w s).1) volume 0 1 :=
    (hz.snd.mul hw.fst).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hi₁ hi₂,← intervalIntegral.integral_const_mul,
    fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
    classicalDiscriminantHamiltonianDirection,ContinuousMap.coe_mk]
  ring

/-- The actual source characteristic/discriminant bracket at finite Fourier
input retains the literal boundary sign and sine normalization. -/
theorem sourceBracket_boundary_discriminant_finite
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z w : ℂ) :
    2*(z-w)*sourceBracket (by norm_num)
      (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z)
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) w)
      (CoeffPair.ofFinsupp (p := 2) a) =
        extensionSign b*(periodOneBoundaryCharacteristic (by simp) (by norm_num) b
          (CoeffPair.ofFinsupp (p := 2) a) z*
            sourceAntiDiscriminantCandidate (by simp) (by norm_num) (CoeffPair.ofFinsupp (p := 2) a) w-
          sourceAntiDiscriminantCandidate (by simp) (by norm_num) (CoeffPair.ofFinsupp (p := 2) a) z*
            periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) w) := by
  rw [sourceBracket_boundary_discriminant_finite_eq_physical,
    periodOneBoundaryCharacteristic_finite_eq_classical,
    periodOneBoundaryCharacteristic_finite_eq_classical,
    sourceAntiDiscriminantCandidate_finite_eq_classical,
    sourceAntiDiscriminantCandidate_finite_eq_classical]
  exact fderiv_classicalSeparatedCharacteristic_hamiltonian b (finiteSourceCurve a) z w

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each fixed spectral section of an actual source characteristic is entire. -/
theorem analyticOnNhd_sourceBoundaryCharacteristic_section
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (z : ℂ) :
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z) univ := by
  intro ψ _
  exact (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b (z,ψ) (mem_univ _)).comp
    (f := fun χ : CoeffPair p => (z,χ)) (analyticAt_const.prod analyticAt_id)

/-- The characteristic/discriminant source flow holds for all complex sources
at every finite exponent at least two, including coincident spectral parameters.
There is no finite identity or physical gradient hypothesis. -/
theorem sourceBracket_boundary_discriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z w : ℂ) :
    2*(z-w)*sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        extensionSign b*(periodOneBoundaryCharacteristic hp hp1 b φ z*sourceAntiDiscriminantCandidate hp hp1 φ w-
          sourceAntiDiscriminantCandidate hp hp1 φ z*periodOneBoundaryCharacteristic hp hp1 b φ w) := by
  let F : ℂ → CoeffPair p → ℂ := fun t ψ => periodOneBoundaryCharacteristic hp hp1 b ψ t
  let G : ℂ → CoeffPair p → ℂ := fun t ψ => canonicalDiscriminant hp (periodOnePotential ψ) t
  let A : ℂ → CoeffPair p → ℂ := fun t ψ => sourceAntiDiscriminantCandidate hp hp1 ψ t
  have hF (t : ℂ) : AnalyticOnNhd ℂ (F t) univ :=
    analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b t
  have hG (t : ℂ) : AnalyticOnNhd ℂ (G t) univ := analyticOnNhd_sourceDiscriminant_section hp hp1 t
  have hA (t : ℂ) : AnalyticOnNhd ℂ (A t) univ := by
    intro ψ _
    exact (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (t,ψ) (mem_univ _)).comp
      (f := fun χ : CoeffPair p => (t,χ)) (analyticAt_const.prod analyticAt_id)
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      2*(z-w)*sourceBracket h2p (F z) (G w) (CoeffPair.ofFinsupp (p := p) a) =
        extensionSign b*(F z (CoeffPair.ofFinsupp (p := p) a)*A w (CoeffPair.ofFinsupp (p := p) a)-
          A z (CoeffPair.ofFinsupp (p := p) a)*F w (CoeffPair.ofFinsupp (p := p) a)) := by
    have hrestrictF (t : ℂ) : F t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b χ t) := by
      funext χ
      exact (congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp
        (by norm_num) hp1 h2p b χ) t).symm
    have hrestrictG (t : ℂ) : G t ∘ CoeffPair.exponentInclusion h2p =
        (fun χ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential χ) t) := by
      funext χ
      exact (sourceDiscriminant_exponent (by simp) hp h2p χ t).symm
    have hc := sourceBracket_restrict_exponent (by norm_num) h2p (F z) (G w)
      (CoeffPair.ofFinsupp (p := 2) a)
      ((hF z _ (mem_univ _)).differentiableAt) ((hG w _ (mem_univ _)).differentiableAt)
    rw [hrestrictF z,hrestrictG w,CoeffPair.exponentInclusion_ofFinsupp] at hc
    rw [← hc]
    have hvalueF (t : ℂ) : F t (CoeffPair.ofFinsupp (p := p) a) =
        periodOneBoundaryCharacteristic (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) t := by
      have h := congrFun (hrestrictF t) (CoeffPair.ofFinsupp (p := 2) a)
      simpa only [Function.comp_apply,CoeffPair.exponentInclusion_ofFinsupp] using h
    have hvalueA (t : ℂ) : A t (CoeffPair.ofFinsupp (p := p) a) =
        sourceAntiDiscriminantCandidate (by simp) (by norm_num) (CoeffPair.ofFinsupp (p := 2) a) t := by
      have h := congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp
        (by norm_num) hp1 h2p (CoeffPair.ofFinsupp (p := 2) a)) t
      rw [CoeffPair.exponentInclusion_ofFinsupp] at h
      exact h.symm
    rw [hvalueF z,hvalueF w,hvalueA z,hvalueA w]
    exact sourceBracket_boundary_discriminant_finite b a z w
  have hcF (t : ℂ) : Continuous (F t) := continuousOn_univ.mp (hF t).continuousOn
  have hcA (t : ℂ) : Continuous (A t) := continuousOn_univ.mp (hA t).continuousOn
  have hcB : Continuous (sourceBracket h2p (F z) (G w)) :=
    continuousOn_univ.mp (analyticOnNhd_sourceBracket h2p (hF z) (hG w)).continuousOn
  have heq : (fun ψ => 2*(z-w)*sourceBracket h2p (F z) (G w) ψ) =
      (fun ψ => extensionSign b*(F z ψ*A w ψ-A z ψ*F w ψ)) :=
    (denseRange_finiteSourcePairs hp).equalizer (continuous_const.mul hcB)
      (continuous_const.mul ((hcF z).mul (hcA w) |>.sub ((hcA z).mul (hcF w)))) (by
        funext a
        exact hfinite a)
  exact congrFun heq φ

/-- At an actual boundary root the fixed-parameter characteristic bracket
reduces to the anti-discriminant times the other characteristic value. -/
theorem sourceBracket_boundary_discriminant_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z w : ℂ)
    (hz : periodOneBoundaryCharacteristic hp hp1 b φ z = 0) :
    2*(z-w)*sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        -extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ z*
          periodOneBoundaryCharacteristic hp hp1 b φ w := by
  rw [sourceBracket_boundary_discriminant hp hp1 h2p,hz]
  ring

/-- The formula applies to every actual canonical Dirichlet or Neumann root.
The root is evaluated at the base source and held fixed in the differentiated
characteristic; this does not differentiate the moving root coordinate. -/
theorem sourceBracket_boundary_discriminant_at_canonicalRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*sourceBracket h2p
      (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ μ)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        -extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*
          periodOneBoundaryCharacteristic hp hp1 b φ w := by
  apply sourceBracket_boundary_discriminant_at_root hp hp1 h2p
  exact (periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b φ _).mpr
    ((canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ _).mpr ⟨n,rfl⟩)

end NLS.ZakharovShabat
