import NLS.Fourier.PeriodicFourierLebesgueSeries
/-! # Function endpoints of the original Fourier–Lebesgue spaces

FL² is linearly isometric to the actual L² quotient on the physical circle,
and the original action and Parseval identity have the exact 1/L interval
normalization. Interval L¹ data has the sharp FL∞ coefficient bound. FL¹ has
a unique continuous, uniformly continuous representative given by its absolutely
and uniformly convergent physical Fourier series, with operator norm at most one.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

def circleL1Functional (g : AddCircle L → ℂ) (hg : Integrable g AddCircle.haarAddCircle) :
    C(AddCircle L,ℂ) →L[ℂ] ℂ :=
  let hi (f : C(AddCircle L,ℂ)) := hg.mul_bdd f.continuous.aestronglyMeasurable (ae_of_all _ f.norm_coe_le_norm)
  let F : C(AddCircle L,ℂ) →ₗ[ℂ] ℂ := {
    toFun f := ∫ x, g x*f x ∂AddCircle.haarAddCircle
    map_add' f h := by
      simp only [ContinuousMap.add_apply,mul_add]
      exact integral_add (hi f) (hi h)
    map_smul' c f := by
      simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
      simp_rw [mul_left_comm (g _) c]
      exact integral_const_mul c _ }
  F.mkContinuous (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle) (by
    intro f
    calc
      _ ≤ ∫ x, ‖g x*f x‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖g x‖*‖f‖ ∂AddCircle.haarAddCircle := by
        apply integral_mono (hi f).norm (hg.norm.mul_const _)
        intro x
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
      _ = _ := integral_mul_const _ _)

namespace SmoothPeriodicTest.Distribution

def ofCircleL1 (g : AddCircle L → ℂ) (hg : Integrable g AddCircle.haarAddCircle) : Distribution L :=
  (circleL1Functional g hg).comp toContinuousCLM

theorem ofCircleL1_apply (g : AddCircle L → ℂ) (hg : Integrable g AddCircle.haarAddCircle)
    (f : SmoothPeriodicTest L) :
    ofCircleL1 g hg f = ∫ x, g x * toContinuousCLM f x ∂AddCircle.haarAddCircle := rfl

theorem ofCircleL1_apply_interval (g : AddCircle L → ℂ) (hg : Integrable g AddCircle.haarAddCircle)
    (f : SmoothPeriodicTest L) :
    ofCircleL1 g hg f = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, g (x : AddCircle L)*f x := by
  rw [ofCircleL1_apply,AddCircle.integral_haarAddCircle,← AddCircle.intervalIntegral_preimage L 0]
  simp only [zero_add,toContinuousCLM_apply,Complex.real_smul,Complex.ofReal_inv]

theorem ofCircleL1_coefficient (g : AddCircle L → ℂ) (hg : Integrable g AddCircle.haarAddCircle) (n : ℤ) :
    ofCircleL1 g hg (mode (-n)) = fourierCoeff g n := by
  have he : toContinuousCLM (mode (-n) : SmoothPeriodicTest L) = fourier (-n) := by
    ext y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [toContinuousCLM_apply,mode_apply_physical,fourier_coe_apply]
    congr 1
    ring
  rw [ofCircleL1_apply,he,fourierCoeff]
  congr 1
  funext x
  exact mul_comm _ _

end SmoothPeriodicTest.Distribution
namespace PeriodicFourierLebesgue

def unweightedCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] : PeriodicFourierLebesgue L Weight.one p ≃ₗᵢ[ℂ] Coeff p :=
  (coefficientsIsometry Weight.one p Weight.hasTemperedInverse_one).trans (WeightedCoeff.weightIsometry Weight.one p)

@[simp] theorem unweightedCoefficients_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : PeriodicFourierLebesgue L Weight.one p) (n : ℤ) :
    unweightedCoefficients p u n = u.val (mode (-n)) := by
  change (Weight.one n : ℂ)*u.val (mode (-n)) = _
  simp

def l2Isometry : PeriodicFourierLebesgue L Weight.one 2 ≃ₗᵢ[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := L)) :=
  (unweightedCoefficients 2).trans fourierBasis.repr.symm

theorem l2Isometry_coefficient (u : PeriodicFourierLebesgue L Weight.one 2) (n : ℤ) :
    fourierCoeff (l2Isometry u) n = u.val (mode (-n)) := by
  rw [← fourierBasis_repr]
  change fourierBasis.repr (fourierBasis.repr.symm (unweightedCoefficients 2 u)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,unweightedCoefficients_apply]

theorem l2Isometry_represents (u : PeriodicFourierLebesgue L Weight.one 2) :
    Distribution.ofCircleL1 (l2Isometry u) ((Lp.memLp (l2Isometry u)).integrable (by norm_num)) = u.val := by
  apply Distribution.ext_coefficients
  intro n
  rw [Distribution.ofCircleL1_coefficient,l2Isometry_coefficient]

theorem l2Isometry_apply (u : PeriodicFourierLebesgue L Weight.one 2) (f : SmoothPeriodicTest L) :
    u.val f = ∫ x, l2Isometry u x * toContinuousCLM f x ∂AddCircle.haarAddCircle := by
  rw [← l2Isometry_represents u,Distribution.ofCircleL1_apply]

theorem l2Isometry_apply_interval (u : PeriodicFourierLebesgue L Weight.one 2) (f : SmoothPeriodicTest L) :
    u.val f = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, l2Isometry u (x : AddCircle L)*f x := by
  rw [← l2Isometry_represents u,Distribution.ofCircleL1_apply_interval]

theorem l2Isometry_norm (u : PeriodicFourierLebesgue L Weight.one 2) : ‖l2Isometry u‖ = ‖u‖ := l2Isometry.norm_map u

theorem l2Isometry_parseval (u : PeriodicFourierLebesgue L Weight.one 2) :
    ‖u‖^2 = ∫ x, ‖l2Isometry u x‖^2 ∂AddCircle.haarAddCircle := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (unweightedCoefficients 2 u)
  have he : HasSum (fun n => ‖u.val (mode (-n))‖^2) (‖u‖^2) := by
    simpa only [unweightedCoefficients_apply,ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] using h
  exact he.unique (by simpa only [l2Isometry_coefficient] using hasSum_sq_fourierCoeff (l2Isometry u))

theorem l2Isometry_parseval_interval (u : PeriodicFourierLebesgue L Weight.one 2) :
    ‖u‖^2 = L⁻¹ * ∫ x in (0:ℝ)..L, ‖l2Isometry u (x : AddCircle L)‖^2 := by
  rw [l2Isometry_parseval,AddCircle.integral_haarAddCircle,← AddCircle.intervalIntegral_preimage L 0]
  simp only [zero_add,smul_eq_mul]

def ofIntervalL1 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) : PeriodicFourierLebesgue L Weight.one ⊤ :=
  ⟨Distribution.ofL1 f hf,by
    change Memℓp (fun n => (Weight.one n : ℂ)*Distribution.ofL1 f hf (mode (-n))) ⊤
    simp only [Weight.one_apply,Complex.ofReal_one,one_mul,Distribution.ofL1_coefficient]
    refine memℓp_infty ⟨periodicL1Size L f,?_⟩
    rintro y ⟨n,rfl⟩
    exact norm_intervalFourierCoefficient_le_L1 L f hf n⟩

theorem norm_ofIntervalL1_le (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    ‖ofIntervalL1 f hf‖ ≤ periodicL1Size L f := by
  rw [← (unweightedCoefficients ⊤).norm_map]
  apply lp.norm_le_of_forall_le (periodicL1Size_nonneg L f)
  intro n
  rw [unweightedCoefficients_apply]
  exact (Distribution.ofL1_coefficient f hf n).symm ▸ norm_intervalFourierCoefficient_le_L1 L f hf n

end PeriodicFourierLebesgue

/-- Absolute convergence in the physical circle's uniform norm. -/
theorem summable_norm_fourierTerms_period (a : Coeff 1) :
    Summable (fun n : ℤ => ‖a n • (fourier n : C(AddCircle L,ℂ))‖) := by
  simpa only [norm_smul,fourier_norm,mul_one] using (lp.memℓp a).norm.summable_of_one

def continuousSynthesisPeriod (a : Coeff 1) : C(AddCircle L,ℂ) := ∑' n : ℤ, a n • fourier n

theorem hasSum_continuousSynthesisPeriod (a : Coeff 1) :
    HasSum (fun n : ℤ => a n • fourier n) (continuousSynthesisPeriod (L := L) a) :=
  (summable_norm_fourierTerms_period (L := L) a).of_norm.hasSum

theorem norm_continuousSynthesisPeriod_le (a : Coeff 1) : ‖continuousSynthesisPeriod (L := L) a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ∑' n, ‖a n • (fourier n : C(AddCircle L,ℂ))‖ := norm_tsum_le_tsum_norm (summable_norm_fourierTerms_period a)
    _ = ‖a‖ := by
      simpa only [norm_smul,fourier_norm,mul_one,ENNReal.toReal_one,Real.rpow_one] using
        (lp.hasSum_norm (p := 1) (by simp) a).tsum_eq

def continuousSynthesisPeriodCLM : Coeff 1 →L[ℂ] C(AddCircle L,ℂ) :=
  LinearMap.mkContinuous
    { toFun := continuousSynthesisPeriod (L := L)
      map_add' := fun a b => by
        change (∑' n, (a n + b n) • fourier n) = _
        simp_rw [add_smul]
        exact (summable_norm_fourierTerms_period (L := L) a).of_norm.tsum_add
          (summable_norm_fourierTerms_period (L := L) b).of_norm
      map_smul' := fun c a => by
        change (∑' n, (c * a n) • fourier n) = _
        simp_rw [mul_smul]
        exact (summable_norm_fourierTerms_period (L := L) a).of_norm.tsum_const_smul c }
    1 (fun a => by simpa using norm_continuousSynthesisPeriod_le (L := L) a)

theorem fourierCoeff_continuousSynthesisPeriod (a : Coeff 1) (n : ℤ) :
    fourierCoeff (continuousSynthesisPeriod (L := L) a) n = a n := by
  let F : C(AddCircle L,ℂ) →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ))
  have hF (f : C(AddCircle L,ℂ)) : F f = fourierCoeff f n :=
    (fourierBasis_repr _ n).trans (fourierCoeff_toLp f n)
  rw [← hF (continuousSynthesisPeriod a)]
  change F (∑' k : ℤ, a k • (fourier k : C(AddCircle L,ℂ))) = a n
  rw [F.map_tsum (summable_norm_fourierTerms_period (L := L) a).of_norm]
  simp only [hF,ContinuousMap.coe_smul,fourierCoeff.const_smul,fourierCoeff_fourier,Pi.single_apply,smul_eq_mul]
  simp

namespace PeriodicFourierLebesgue

def continuousRepresentative (u : PeriodicFourierLebesgue L Weight.one 1) : C(AddCircle L,ℂ) :=
  continuousSynthesisPeriod (unweightedCoefficients 1 u)

def continuousRepresentativeCLM : PeriodicFourierLebesgue L Weight.one 1 →L[ℂ] C(AddCircle L,ℂ) :=
  continuousSynthesisPeriodCLM.comp (unweightedCoefficients 1).toContinuousLinearEquiv.toContinuousLinearMap

theorem continuousRepresentativeCLM_apply (u : PeriodicFourierLebesgue L Weight.one 1) :
    continuousRepresentativeCLM u = continuousRepresentative u := rfl

theorem continuousRepresentative_coefficient (u : PeriodicFourierLebesgue L Weight.one 1) (n : ℤ) :
    fourierCoeff (continuousRepresentative u) n = u.val (mode (-n)) := by
  rw [continuousRepresentative,fourierCoeff_continuousSynthesisPeriod,unweightedCoefficients_apply]

theorem continuousRepresentative_represents (u : PeriodicFourierLebesgue L Weight.one 1) :
    Distribution.ofContinuous (continuousRepresentative u) = u.val := by
  apply Distribution.ext_coefficients
  intro n
  rw [Distribution.ofContinuous_coefficient,continuousRepresentative_coefficient]

theorem existsUnique_continuousRepresentative (u : PeriodicFourierLebesgue L Weight.one 1) :
    ∃! f : C(AddCircle L,ℂ), Distribution.ofContinuous f = u.val :=
  ⟨continuousRepresentative u,continuousRepresentative_represents u,fun _f hf =>
    Distribution.ofContinuous_injective (hf.trans (continuousRepresentative_represents u).symm)⟩

theorem norm_continuousRepresentative_le (u : PeriodicFourierLebesgue L Weight.one 1) :
    ‖continuousRepresentative u‖ ≤ ‖u‖ :=
  (norm_continuousSynthesisPeriod_le _).trans_eq ((unweightedCoefficients 1).norm_map u)

theorem hasSum_continuousRepresentative (u : PeriodicFourierLebesgue L Weight.one 1) :
    HasSum (fun n : ℤ => u.val (mode (-n)) • fourier n) (continuousRepresentative u) := by
  simpa only [unweightedCoefficients_apply,continuousRepresentative] using hasSum_continuousSynthesisPeriod (L := L) (unweightedCoefficients 1 u)

theorem summable_norm_continuousRepresentative (u : PeriodicFourierLebesgue L Weight.one 1) :
    Summable (fun n : ℤ => ‖u.val (mode (-n)) • (fourier n : C(AddCircle L,ℂ))‖) := by
  simpa only [unweightedCoefficients_apply] using summable_norm_fourierTerms_period (L := L) (unweightedCoefficients 1 u)

theorem uniformlyContinuous_continuousRepresentative (u : PeriodicFourierLebesgue L Weight.one 1) :
    UniformContinuous (continuousRepresentative u) := CompactSpace.uniformContinuous_of_continuous (continuousRepresentative u).continuous

theorem continuousRepresentative_apply (u : PeriodicFourierLebesgue L Weight.one 1) (x : ℝ) :
    continuousRepresentative u (x : AddCircle L) =
      ∑' n : ℤ, u.val (mode (-n)) * Complex.exp (2*Real.pi*Complex.I*n*x/L) := by
  have h := (ContinuousMap.evalCLM ℂ (x : AddCircle L)).hasSum (hasSum_continuousRepresentative u)
  exact (by simpa only [ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,smul_eq_mul,fourier_coe_apply] using h.tsum_eq.symm)

end PeriodicFourierLebesgue
end NLS.Fourier
