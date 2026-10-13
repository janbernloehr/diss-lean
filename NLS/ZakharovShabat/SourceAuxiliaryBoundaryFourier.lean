import NLS.ZakharovShabat.SourceBoundaryFourier
import NLS.ZakharovShabat.BoundedAuxiliaryExtension
import NLS.ZakharovShabat.SourceLemma5_1

/-!
# Auxiliary Fourier expansions (1.11)–(1.12)

Both auxiliary reflections have convergent series in the original coefficient
and physical L² norms, with amplitude half the physical sesquilinear pairing.
Their sums reconstruct the actual reflected interval data and retain its energy.
The second line of printed (1.11) incorrectly uses an ordinary Dirichlet mode;
these theorems use the auxiliary mode defined alongside that equation. The raw
component formula and the normalization require no change. No endpoint matching,
uniform convergence or H¹ convergence is assumed for arbitrary L² input.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The auxiliary phase is an isometry for the original component-sum coefficient norm. -/
def sourceAuxiliaryPhaseTwo : CoeffPair 2 ≃ₗᵢ[ℂ] CoeffPair 2 where
  toFun u := WithLp.toLp 2 (u.ofLp.1, Complex.I • u.ofLp.2)
  invFun u := WithLp.toLp 2 (u.ofLp.1, -Complex.I • u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [smul_add]
  map_smul' c u := by
    apply WithLp.ofLp_injective
    exact Prod.ext rfl (smul_comm Complex.I c u.ofLp.2)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg u)).mp
    simp [WithLp.prod_norm_sq_eq_of_L2, norm_smul]

/-- The printed auxiliary mode has the phase on its positive component. -/
def physicalAuxiliaryBoundaryMode (b : BoundaryCondition) (n : ℤ) (x : ℝ) : ℂ × ℂ :=
  (extensionSign b * wave (-n) x, Complex.I * wave n x)

/-- The original-norm coefficient vector of the unnormalized auxiliary mode. -/
def sourceAuxiliaryBoundaryMode (b : BoundaryCondition) (n : ℤ) : CoeffPair 2 :=
  sourceAuxiliaryPhaseTwo (sourceBoundaryMode b n)

/-- The physical sesquilinear pairing with the auxiliary mode. -/
def intervalAuxiliaryBoundaryPairing (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (f x).1 * starRingEnd ℂ ((physicalAuxiliaryBoundaryMode b n x).1) +
    (f x).2 * starRingEnd ℂ ((physicalAuxiliaryBoundaryMode b n x).2)

theorem intervalAuxiliaryBoundaryPairing_eq_phase (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (n : ℤ) :
    intervalAuxiliaryBoundaryPairing b f n = intervalBoundaryPairing b (physicalAuxiliaryPhase.symm f) n := by
  unfold intervalAuxiliaryBoundaryPairing intervalBoundaryPairing
  apply intervalIntegral.integral_congr
  intro x _
  cases b <;> simp [physicalAuxiliaryBoundaryMode, physicalAuxiliaryPhase_symm_apply,
    extensionSign, ← wave_neg] <;> ring

/-- Inverse phase preserves square integrability on the original interval. -/
theorem memLp_physicalAuxiliaryPhase_symm (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (physicalAuxiliaryPhase.symm f) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨hf.fst, hf.snd.const_smul (-Complex.I)⟩

/-- The original auxiliary L² reflection, represented in the component-sum coefficient space. -/
def sourceAuxiliaryIntervalExtensionCoefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  sourceAuxiliaryPhaseTwo (sourceIntervalExtensionCoefficients b (physicalAuxiliaryPhase.symm f)
    (memLp_physicalAuxiliaryPhase_symm f hf))

/-- The auxiliary series has exactly half the original physical pairing as amplitude. -/
theorem sourceEquation1_11_1_12_coefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n : ℤ => ((1/2 : ℂ) * intervalAuxiliaryBoundaryPairing b f n) •
      sourceAuxiliaryBoundaryMode b n) (sourceAuxiliaryIntervalExtensionCoefficients b f hf) := by
  let L : CoeffPair 2 →L[ℂ] CoeffPair 2 := sourceAuxiliaryPhaseTwo.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasSum
    (hasSum_sourceIntervalExtensionCoefficients b (physicalAuxiliaryPhase.symm f)
      (memLp_physicalAuxiliaryPhase_symm f hf))
  convert h using 1
  · funext n
    rw [ContinuousLinearMap.map_smul, intervalAmplitude_eq_half_pairing b _
      (memLp_physicalAuxiliaryPhase_symm f hf), ← intervalAuxiliaryBoundaryPairing_eq_phase]
    rfl
  · rfl

/-- Both original auxiliary components are actual normalized physical Fourier coefficients. -/
theorem sourceAuxiliaryIntervalExtensionCoefficients_integrals (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceAuxiliaryIntervalExtensionCoefficients b f hf).fst n =
      periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).1) n ∧
    (sourceAuxiliaryIntervalExtensionCoefficients b f hf).snd n =
      periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).2) n := by
  constructor
  · rfl
  · change Complex.I * periodTwoCoefficient
      (fun x => (intervalExtension b (physicalAuxiliaryPhase.symm f) x).2) n =
      periodTwoCoefficient (fun x => Complex.I * (intervalExtension b (physicalAuxiliaryPhase.symm f) x).2) n
    rw [periodTwoCoefficient_const_mul]

/-- The ordinary mode printed in (1.11)'s second line is different even at zero frequency. -/
theorem physicalAuxiliaryBoundaryMode_ne_ordinary_zero :
    physicalAuxiliaryBoundaryMode .dirichlet 0 0 ≠ physicalBoundaryMode .dirichlet 0 0 := by
  intro h
  have hi := congrArg (fun z : ℂ × ℂ => (z.2).im) h
  norm_num [physicalAuxiliaryBoundaryMode, physicalBoundaryMode, wave] at hi

/-- Original physical L² synthesis intertwines the auxiliary phase almost everywhere. -/
theorem sourceCircleRepresentative_auxiliaryPhaseTwo (a : CoeffPair 2) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceAuxiliaryPhaseTwo a))
      =ᵐ[volume.restrict (Ioc 0 2)]
      physicalAuxiliaryPhase (sourceCircleRepresentative (sourceCircleSynthesis a)) := by
  change physicalBase (auxiliaryPhase (Coeff 2) (CoeffPair.toMax 2 a)) =ᵐ[_]
    physicalAuxiliaryPhase (physicalBase (CoeffPair.toMax 2 a))
  have h := circle_ae_pullback (Lp.coeFn_smul Complex.I (l2Synthesis a.snd))
  filter_upwards [h] with x hx
  change (circlePullback (l2Synthesis a.fst) x,
    circlePullback (l2Synthesis (Complex.I • a.snd)) x) = _
  rw [map_smul]
  exact Prod.ext rfl hx

/-- The original coefficient sum reconstructs the actual auxiliary reflection. -/
theorem sourceCircleSynthesis_auxiliaryIntervalExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceAuxiliaryIntervalExtensionCoefficients b f hf))
      =ᵐ[volume.restrict (Ioc 0 2)] auxiliaryIntervalExtension b f := by
  have h := sourceCircleSynthesis_intervalExtension b (physicalAuxiliaryPhase.symm f)
    (memLp_physicalAuxiliaryPhase_symm f hf)
  have hg := sourceCircleRepresentative_auxiliaryPhaseTwo
    (sourceIntervalExtensionCoefficients b (physicalAuxiliaryPhase.symm f) (memLp_physicalAuxiliaryPhase_symm f hf))
  filter_upwards [hg, h] with x hx hy
  exact hx.trans (congrArg (auxiliaryPhase ℂ) hy)

/-- The coefficient basis represents the literal physical auxiliary waves. -/
theorem sourceAuxiliaryBoundaryMode_physical (b : BoundaryCondition) (n : ℤ) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceAuxiliaryBoundaryMode b n))
      =ᵐ[volume.restrict (Ioc 0 2)] physicalAuxiliaryBoundaryMode b n := by
  filter_upwards [sourceCircleRepresentative_auxiliaryPhaseTwo (sourceBoundaryMode b n),
    sourceBoundaryMode_physical b n] with x hx hy
  exact hx.trans (congrArg (auxiliaryPhase ℂ) hy)

/-- The corrected auxiliary series converges in the original normalized physical L² norm. -/
theorem sourceEquation1_11_1_12_L2 (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n : ℤ => ((1/2 : ℂ) * intervalAuxiliaryBoundaryPairing b f n) •
      sourceCircleSynthesis (sourceAuxiliaryBoundaryMode b n))
      (sourceCircleSynthesis (sourceAuxiliaryIntervalExtensionCoefficients b f hf)) := by
  let L : CoeffPair 2 →L[ℂ] SourceCirclePairL2 := sourceCircleSynthesis.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasSum (sourceEquation1_11_1_12_coefficients b f hf)
  convert h using 1
  · funext n
    exact (L.map_smul _ _).symm
  · rfl

/-- Auxiliary reflection preserves the original interval energy with normalized period two. -/
theorem norm_sourceAuxiliaryIntervalExtensionCoefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ‖sourceAuxiliaryIntervalExtensionCoefficients b f hf‖ = ‖intervalL2OfFunction f hf‖ := by
  rw [sourceAuxiliaryIntervalExtensionCoefficients, LinearIsometryEquiv.norm_map,
    norm_sourceIntervalExtensionCoefficients]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_intervalL2OfFunction, norm_sq_intervalL2OfFunction]
  simp [physicalAuxiliaryPhase_symm_apply]

/-- The entire auxiliary Fourier expansion, including the actual sum and original energy. -/
theorem sourceEquation1_11_1_12 (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ∃ F : SourceCirclePairL2,
      sourceCircleRepresentative F =ᵐ[volume.restrict (Ioc 0 2)] auxiliaryIntervalExtension b f ∧
      HasSum (fun n : ℤ => ((1/2 : ℂ) * intervalAuxiliaryBoundaryPairing b f n) •
        sourceCircleSynthesis (sourceAuxiliaryBoundaryMode b n)) F ∧
      ‖F‖ ^ 2 = (∫ x in (0 : ℝ)..1, ‖(f x).1‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖(f x).2‖ ^ 2 := by
  refine ⟨sourceCircleSynthesis (sourceAuxiliaryIntervalExtensionCoefficients b f hf),
    sourceCircleSynthesis_auxiliaryIntervalExtension b f hf, sourceEquation1_11_1_12_L2 b f hf, ?_⟩
  rw [sourceCircleSynthesis.norm_map, norm_sourceAuxiliaryIntervalExtensionCoefficients,
    norm_sq_intervalL2OfFunction]

/-- The component formula preceding (1.11), with both auxiliary signs. -/
theorem sourceAuxiliaryIntervalExtensionCoefficients_raw (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceAuxiliaryIntervalExtensionCoefficients b f hf).fst n =
      halfCoefficient (fun x => (f x).1) n - Complex.I * extensionSign b * halfCoefficient (fun x => (f x).2) (-n) ∧
    (sourceAuxiliaryIntervalExtensionCoefficients b f hf).snd n =
      halfCoefficient (fun x => (f x).2) n + Complex.I * extensionSign b * halfCoefficient (fun x => (f x).1) (-n) := by
  have h₁ : IntervalIntegrable (fun x => (f x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (f x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.snd.integrable (by norm_num))
  obtain ⟨he₁, he₂⟩ := sourceAuxiliaryIntervalExtensionCoefficients_integrals b f hf n
  rw [he₁, he₂, auxiliaryIntervalExtension_fst, auxiliaryIntervalExtension_snd,
    periodTwoCoefficient_folded_of_intervalIntegrable _ h₁ h₂,
    periodTwoCoefficient_folded_of_intervalIntegrable _ h₂ h₁]
  constructor <;> ring

/-- Constant auxiliary zero-mode data are square integrable on the original interval. -/
theorem memLp_auxiliaryZeroMode : MemLp (fun _ : ℝ => ((1 : ℂ), Complex.I)) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_two_interval continuous_const 0 1 (by norm_num),
    memLp_two_interval continuous_const 0 1 (by norm_num)⟩

/-- The second line of printed (1.11) fails for a constant auxiliary zero mode. -/
theorem sourceEquation1_11_printed_ordinary_mode_false :
    ¬ HasSum (fun n : ℤ => ((1/2 : ℂ) * intervalAuxiliaryBoundaryPairing .dirichlet
      (fun _ => ((1 : ℂ), Complex.I)) n) • sourceBoundaryMode .dirichlet n)
      (sourceAuxiliaryIntervalExtensionCoefficients .dirichlet _ memLp_auxiliaryZeroMode) := by
  intro h
  let f : ℝ → ℂ × ℂ := fun _ => (1, Complex.I)
  let hg := memLp_physicalAuxiliaryPhase_symm f memLp_auxiliaryZeroMode
  have hs := hasSum_sourceIntervalExtensionCoefficients .dirichlet (physicalAuxiliaryPhase.symm f) hg
  simp only [intervalAmplitude_eq_half_pairing .dirichlet _ hg,
    ← intervalAuxiliaryBoundaryPairing_eq_phase] at hs
  have he := congrArg (fun a : CoeffPair 2 => a.snd 0) (h.unique hs)
  change Complex.I * (sourceIntervalExtensionCoefficients .dirichlet (physicalAuxiliaryPhase.symm f) hg).snd 0 =
    (sourceIntervalExtensionCoefficients .dirichlet (physicalAuxiliaryPhase.symm f) hg).snd 0 at he
  have ha : (sourceIntervalExtensionCoefficients .dirichlet (physicalAuxiliaryPhase.symm f) hg).snd 0 = 1 := by
    rw [sourceIntervalExtensionCoefficients_snd]
    change intervalAmplitude .dirichlet (fun _ => ((1 : ℂ), -Complex.I * Complex.I)) 0 = 1
    rw [intervalAmplitude_const_zero]
    norm_num [extensionSign]
  rw [ha, mul_one] at he
  have hi := congrArg Complex.im he
  norm_num at hi

/-- The L² Fourier sum agrees exactly with the original auxiliary Sobolev extension. -/
theorem sourceAuxiliaryIntervalExtensionCoefficients_eq_classical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (hL : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceAuxiliaryIntervalExtensionCoefficients b f hL = sourceDomainInclusion (sourceClassicalAuxiliaryExtension b f hf) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (sourceAuxiliaryIntervalExtensionCoefficients b f hL).fst n =
      (sourceDomainInclusion (sourceClassicalAuxiliaryExtension b f hf)).fst n
    rw [sourceDomainInclusion_fst_apply]
    exact (sourceAuxiliaryIntervalExtensionCoefficients_integrals b f hL n).1.trans
      (sourceClassicalAuxiliaryExtension_coefficients b f hf n).1.symm
  · change (sourceAuxiliaryIntervalExtensionCoefficients b f hL).snd n =
      (sourceDomainInclusion (sourceClassicalAuxiliaryExtension b f hf)).snd n
    rw [sourceDomainInclusion_snd_apply]
    exact (sourceAuxiliaryIntervalExtensionCoefficients_integrals b f hL n).2.trans
      (sourceClassicalAuxiliaryExtension_coefficients b f hf n).2.symm

end NLS.ZakharovShabat
