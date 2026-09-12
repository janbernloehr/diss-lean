import NLS.Fourier.CircleMultiplication

/-!
# Convolution is physical multiplication at the Hilbert exponent

An arbitrary square-integrable potential is multiplied by a uniformly
convergent Fourier series. The result is exactly the Hilbert synthesis of the
discrete `ℓ2 × ℓ1` convolution, with no finite-support or smoothness assumption
on the potential. The Sobolev case identifies the existing potential operator.
-/

noncomputable section
open MeasureTheory
namespace NLS.Fourier
open ZakharovShabat

/-- Multiplication by a Fourier wave shifts every physical Fourier coefficient. -/
theorem fourierCoeff_circleMul_fourier (g : CircleL2) (k n : ℤ) :
    fourierCoeff (circleMul (fourier k) g) n = fourierCoeff g (n - k) := by
  rw [fourierCoeff_congr_ae (coeFn_circleMul (fourier k) g)]
  change (∫ x, fourier (-n) x * (fourier k x * g x) ∂AddCircle.haarAddCircle) =
    ∫ x, fourier (-(n - k)) x * g x ∂AddCircle.haarAddCircle
  congr 1
  funext x
  rw [← mul_assoc, ← fourier_add, show -n + k = -(n - k) by ring]

/-- Coefficient translation synthesizes to multiplication by the corresponding physical wave. -/
theorem circleMul_fourier_l2Synthesis (φ : Coeff 2) (k : ℤ) :
    circleMul (fourier k) (l2Synthesis φ) = l2Synthesis (Coeff.shift k φ) := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_circleMul_fourier,
    fourierCoeff_l2Synthesis, fourierCoeff_l2Synthesis]
  rfl

/-- A Fourier wave preserves the norm of every physical `L²` potential. -/
theorem norm_circleMul_fourier (g : CircleL2) (k : ℤ) : ‖circleMul (fourier k) g‖ = ‖g‖ := by
  obtain ⟨φ, rfl⟩ := l2Synthesis.surjective g
  rw [circleMul_fourier_l2Synthesis, norm_l2Synthesis, norm_l2Synthesis, Coeff.norm_shift]

/-- Every `ℓ2 × ℓ1` convolution is the actual `L²` product of its two physical realizations. -/
theorem circleMul_continuousSynthesis (φ : Coeff 2) (a : Coeff 1) :
    circleMul (continuousSynthesis a) (l2Synthesis φ) = l2Synthesis (Coeff.convolution φ a) := by
  have h₁ := (circleMulCLM.flip (l2Synthesis φ)).hasSum (hasSum_continuousSynthesis a)
  have h₂ := l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (Coeff.summable_convolution_terms φ a).hasSum
  simp only [map_smul, ContinuousLinearMap.flip_apply, circleMulCLM_apply,
    circleMul_fourier_l2Synthesis] at h₁
  simp only [map_smul] at h₂
  exact h₁.unique h₂

/-- The one-derivative coefficient potential operator realizes physical multiplication. -/
theorem l2Synthesis_potentialMul (φ : Coeff 2) (a : ScalarDomain 2) :
    l2Synthesis (potentialMul (by simp) φ a) =
      circleMul (sobolevSynthesis (by simp) a) (l2Synthesis φ) := by
  exact (circleMul_continuousSynthesis φ (WeightedCoeff.sobolevToL1CLM 2 (by simp) a)).symm

/-- The convolution coefficients are the normalized Fourier integrals of the physical product. -/
theorem fourierCoeff_circleMul_sobolevSynthesis (φ : Coeff 2) (a : ScalarDomain 2) (n : ℤ) :
    fourierCoeff (circleMul (sobolevSynthesis (by simp) a) (l2Synthesis φ)) n =
      ∑' k : ℤ, φ (n - k) * a.val k := by
  rw [← l2Synthesis_potentialMul, fourierCoeff_l2Synthesis, potentialMul_apply]

/-- On a full physical period, the synthesized potential product equals pointwise multiplication. -/
theorem circlePullback_potentialMul (φ : Coeff 2) (a : ScalarDomain 2) :
    circlePullback (l2Synthesis (potentialMul (by simp) φ a))
      =ᵐ[volume.restrict (Set.Ioc 0 2)]
      (fun x : ℝ => circlePullback (l2Synthesis φ) x *
        sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) := by
  rw [l2Synthesis_potentialMul]
  simpa only [mul_comm] using circlePullback_circleMul (sobolevSynthesis (by simp) a) (l2Synthesis φ)

/-- The physical product is square integrable on the full period. -/
theorem memLp_physical_potentialMul (φ : Coeff 2) (a : ScalarDomain 2) :
    MemLp (fun x : ℝ => circlePullback (l2Synthesis φ) x *
      sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 2 (volume.restrict (Set.Ioc 0 2)) :=
  (memLp_congr_ae (circlePullback_potentialMul φ a)).mp (memLp_circlePullback _)

/-- Actual normalized real-interval integrals recover the potential product coefficients. -/
theorem periodTwoCoefficient_physical_potentialMul (φ : Coeff 2) (a : ScalarDomain 2) (n : ℤ) :
    periodTwoCoefficient (fun x : ℝ => circlePullback (l2Synthesis φ) x *
      sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) n = potentialMul (by simp) φ a n := by
  have h := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2)
    (circlePullback_potentialMul φ a)) n
  simpa only [← periodTwoCoefficient_eq_fourierCoeffOn, periodTwoCoefficient_circlePullback,
    fourierCoeff_l2Synthesis] using h.symm

end NLS.Fourier
