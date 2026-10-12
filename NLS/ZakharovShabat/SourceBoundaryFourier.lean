import NLS.ZakharovShabat.SourceLemma4_1
import NLS.SequenceSpaces.Truncation
import NLS.Fourier.FoldedEnergy
import NLS.ZakharovShabat.PhysicalIntervalL2

/-! # Fourier representations (1.8)–(1.9)

The printed boundary-mode series converges in the original component-sum
coefficient norm and in the normalized physical period-two L² norm. Its
limit is the actual signed reflection of arbitrary original L² interval
data. The coefficient is exactly half the physical sesquilinear pairing.
Endpoint matching is not assumed, so no uniform or H¹ convergence is claimed.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Assemble the signed reflected coefficient pair from its scalar amplitudes. -/
def sourceBoundaryAssembly (b : BoundaryCondition) : Coeff 2 →L[ℂ] CoeffPair 2 :=
  (CoeffPair.toMax 2).symm.toContinuousLinearMap.comp
    ((extensionSign b • (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap).prod
      (ContinuousLinearMap.id ℂ (Coeff 2)))

/-- Exact original-norm Fourier coefficients of the signed interval extension. -/
def sourceIntervalExtensionCoefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  (CoeffPair.toMax 2).symm
    (periodTwoL2Coefficients (fun x => (intervalExtension b f x).1) (memLp_intervalExtension b f hf).fst,
      periodTwoL2Coefficients (fun x => (intervalExtension b f x).2) (memLp_intervalExtension b f hf).snd)

/-- The second coefficient is the printed half-interval amplitude. -/
theorem sourceIntervalExtensionCoefficients_snd (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceIntervalExtensionCoefficients b f hf).snd n = intervalAmplitude b f n := by
  have h₁ : IntervalIntegrable (fun x => (f x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (f x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.snd.integrable (by norm_num))
  exact periodTwoCoefficient_folded_of_intervalIntegrable (extensionSign b) h₂ h₁ n

/-- The first coefficient reverses the frequency and carries the boundary sign. -/
theorem sourceIntervalExtensionCoefficients_fst (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceIntervalExtensionCoefficients b f hf).fst n = extensionSign b * intervalAmplitude b f (-n) := by
  have h₁ : IntervalIntegrable (fun x => (f x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (f x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.snd.integrable (by norm_num))
  change periodTwoCoefficient (folded (extensionSign b) (fun x => (f x).1) (fun x => (f x).2)) n = _
  rw [periodTwoCoefficient_folded_of_intervalIntegrable (extensionSign b) h₁ h₂]
  simp only [intervalAmplitude, neg_neg]
  cases b <;> simp [extensionSign]
  ring

/-- The full original-norm extension is assembled from the same scalar amplitudes. -/
theorem sourceIntervalExtensionCoefficients_eq_assembly (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceIntervalExtensionCoefficients b f hf =
      sourceBoundaryAssembly b (sourceIntervalExtensionCoefficients b f hf).snd := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · apply lp.ext
    funext n
    change (sourceIntervalExtensionCoefficients b f hf).fst n =
      extensionSign b * (sourceIntervalExtensionCoefficients b f hf).snd (-n)
    rw [sourceIntervalExtensionCoefficients_fst, sourceIntervalExtensionCoefficients_snd]
  · rfl

/-- The printed unnormalized boundary mode in the original coefficient space. -/
def sourceBoundaryMode (b : BoundaryCondition) (n : ℤ) : CoeffPair 2 :=
  sourceBoundaryAssembly b (lp.single 2 n 1)

/-- The series converges in the original component-sum coefficient norm. -/
theorem hasSum_sourceIntervalExtensionCoefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n : ℤ => intervalAmplitude b f n • sourceBoundaryMode b n)
      (sourceIntervalExtensionCoefficients b f hf) := by
  have h := (sourceBoundaryAssembly b).hasSum
    (lp.hasSum_single (by simp) (sourceIntervalExtensionCoefficients b f hf).snd)
  rw [← sourceIntervalExtensionCoefficients_eq_assembly] at h
  convert h using 1
  funext n
  rw [sourceIntervalExtensionCoefficients_snd]
  unfold sourceBoundaryMode
  rw [← map_smul, ← lp.single_smul]
  simp

/-- Physical period-two L² pairs with the sum of the two component energies. -/
def SourceCirclePairL2 := WithLp 2 (CircleL2 × CircleL2)

instance : NormedAddCommGroup SourceCirclePairL2 :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (CircleL2 × CircleL2)))
instance : NormedSpace ℂ SourceCirclePairL2 :=
  inferInstanceAs (NormedSpace ℂ (WithLp 2 (CircleL2 × CircleL2)))

/-- The physical period-two Fourier inverse with the exact component-sum norm. -/
def sourceCircleSynthesis : CoeffPair 2 ≃ₗᵢ[ℂ] SourceCirclePairL2 :=
  l2Synthesis.withLpProdCongr 2 l2Synthesis

/-- The same series converges in the normalized physical period-two L² norm. -/
theorem hasSum_intervalExtension_L2 (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n : ℤ => intervalAmplitude b f n • sourceCircleSynthesis (sourceBoundaryMode b n))
      (sourceCircleSynthesis (sourceIntervalExtensionCoefficients b f hf)) := by
  let L : CoeffPair 2 →L[ℂ] SourceCirclePairL2 := sourceCircleSynthesis.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasSum (hasSum_sourceIntervalExtensionCoefficients b f hf)
  convert h using 1
  · funext n
    exact (L.map_smul (intervalAmplitude b f n) (sourceBoundaryMode b n)).symm
  · rfl

/-- A physical representative of the original pair of period-two L² classes. -/
def sourceCircleRepresentative (u : SourceCirclePairL2) (x : ℝ) : ℂ × ℂ :=
  (circlePullback ((u : WithLp 2 (CircleL2 × CircleL2)).ofLp.1) x,
    circlePullback ((u : WithLp 2 (CircleL2 × CircleL2)).ofLp.2) x)

/-- The L² sum represents the actual reflected function almost everywhere. -/
theorem sourceCircleSynthesis_intervalExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceIntervalExtensionCoefficients b f hf))
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b f := by
  filter_upwards [circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension b f hf).fst,
    circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension b f hf).snd] with x hx hy
  exact Prod.ext hx hy

/-- The printed boundary modes: (epsilon * exp(-i*pi*n*x), exp(i*pi*n*x)). -/
def physicalBoundaryMode (b : BoundaryCondition) (n : ℤ) (x : ℝ) : ℂ × ℂ :=
  (extensionSign b * wave (-n) x, wave n x)

/-- The source basis agrees with the established signed free eigenmode. -/
theorem sourceBoundaryMode_eq (b : BoundaryCondition) (n : ℤ) :
    sourceBoundaryMode b n = (CoeffPair.toMax 2).symm (domainInclusion (mode b n)) := by
  apply (CoeffPair.toMax 2).injective
  cases b <;> apply Prod.ext <;> apply lp.ext <;> funext k <;>
    simp [sourceBoundaryMode, sourceBoundaryAssembly, extensionSign, mode, dirichletMode, neumannMode,
      positiveMode, negativeMode, Coeff.reflection_apply,
      lp.single_apply, Pi.single_apply, neg_eq_iff_eq_neg]

/-- The L² basis vectors represent exactly the printed physical waves. -/
theorem sourceBoundaryMode_physical (b : BoundaryCondition) (n : ℤ) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceBoundaryMode b n))
      =ᵐ[volume.restrict (Ioc 0 2)] physicalBoundaryMode b n := by
  change physicalBase (CoeffPair.toMax 2 (sourceBoundaryMode b n)) =ᵐ[volume.restrict (Ioc 0 2)] _
  rw [sourceBoundaryMode_eq, ContinuousLinearEquiv.apply_symm_apply]
  filter_upwards [physicalBase_domainInclusion (mode (p := 2) b n)] with x hx
  rw [hx]
  cases b <;> simp [physicalDomain, physicalBoundaryMode, mode, dirichletMode, neumannMode,
    positiveMode, negativeMode, extensionSign, sobolevSynthesis_scalarMode]

/-- The full physical interval pairing, without the half coefficient. -/
def intervalBoundaryPairing (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (f x).2 * wave (-n) x + extensionSign b * ((f x).1 * wave n x)

/-- The coefficient in (1.8)–(1.9) is exactly half the physical pairing. -/
theorem intervalAmplitude_eq_half_pairing (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    intervalAmplitude b f n = (1 / 2 : ℂ) * intervalBoundaryPairing b f n := by
  have h₁ : IntervalIntegrable (fun x => (f x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (f x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.snd.integrable (by norm_num))
  unfold intervalBoundaryPairing intervalAmplitude halfCoefficient
  rw [intervalIntegral.integral_add (h₂.mul_continuousOn (continuous_wave (-n)).continuousOn)
    ((h₁.mul_continuousOn (continuous_wave n).continuousOn).const_mul (extensionSign b)),
    intervalIntegral.integral_const_mul]
  simp only [neg_neg]
  ring

/-- This is the original sesquilinear component-sum pairing, conjugate in the mode. -/
theorem intervalBoundaryPairing_eq_integral (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (n : ℤ) :
    intervalBoundaryPairing b f n = ∫ x in (0 : ℝ)..1,
      (f x).1 * starRingEnd ℂ ((physicalBoundaryMode b n x).1) +
        (f x).2 * starRingEnd ℂ ((physicalBoundaryMode b n x).2) := by
  apply intervalIntegral.integral_congr
  intro x _
  cases b <;> simp [physicalBoundaryMode, extensionSign, ← wave_neg] <;> ring

/-- Both printed Fourier series, with their half normalization, for arbitrary L² input. -/
theorem sourceEquation1_8_1_9_L2 (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n : ℤ => ((1 / 2 : ℂ) * intervalBoundaryPairing b f n) •
        sourceCircleSynthesis (sourceBoundaryMode b n))
      (sourceCircleSynthesis (sourceIntervalExtensionCoefficients b f hf)) := by
  simpa only [intervalAmplitude_eq_half_pairing b f hf] using hasSum_intervalExtension_L2 b f hf

/-- Reflection preserves the original interval energy after normalizing the doubled period. -/
theorem norm_sourceIntervalExtensionCoefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ‖sourceIntervalExtensionCoefficients b f hf‖ = ‖intervalL2OfFunction f hf‖ := by
  have hs : ‖extensionSign b‖ = 1 := by cases b <;> simp [extensionSign]
  have he : ‖sourceIntervalExtensionCoefficients b f hf‖ ^ 2 = ‖intervalL2OfFunction f hf‖ ^ 2 := by
    rw [sourceIntervalExtensionCoefficients, CoeffPair.toMax_symm_apply, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [norm_sq_periodTwoL2Coefficients, norm_sq_periodTwoL2Coefficients, norm_sq_intervalL2OfFunction]
    change (1/2 : ℝ) * (∫ x in (0 : ℝ)..2, ‖folded (extensionSign b) (fun t => (f t).1) (fun t => (f t).2) x‖^2) +
      (1/2 : ℝ) * (∫ x in (0 : ℝ)..2, ‖folded (extensionSign b) (fun t => (f t).2) (fun t => (f t).1) x‖^2) = _
    rw [integral_sq_folded_of_memLp (extensionSign b) hs hf.fst hf.snd,
      integral_sq_folded_of_memLp (extensionSign b) hs hf.snd hf.fst]
    ring
  nlinarith [norm_nonneg (sourceIntervalExtensionCoefficients b f hf), norm_nonneg (intervalL2OfFunction f hf)]

/-- The full printed expansion and its actual physical sum, for arbitrary interval H¹ input. -/
theorem sourceEquation1_8_1_9 (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (h₁ : HasIntervalH1Regularity (fun x => (f x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (f x).2)) :
    ∃ F : SourceCirclePairL2,
      sourceCircleRepresentative F =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b f ∧
      HasSum (fun n : ℤ => ((1 / 2 : ℂ) * intervalBoundaryPairing b f n) •
        sourceCircleSynthesis (sourceBoundaryMode b n)) F ∧
      ‖F‖ ^ 2 = (∫ x in (0 : ℝ)..1, ‖(f x).1‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖(f x).2‖ ^ 2 := by
  have hf : MemLp f 2 (volume.restrict (Ioc 0 1)) :=
    memLp_prod_iff.mpr ⟨memLp_of_intervalH1Regularity h₁, memLp_of_intervalH1Regularity h₂⟩
  refine ⟨sourceCircleSynthesis (sourceIntervalExtensionCoefficients b f hf),
    sourceCircleSynthesis_intervalExtension b f hf, sourceEquation1_8_1_9_L2 b f hf, ?_⟩
  rw [sourceCircleSynthesis.norm_map, norm_sourceIntervalExtensionCoefficients, norm_sq_intervalL2OfFunction]

end NLS.ZakharovShabat
