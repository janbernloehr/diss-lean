import NLS.Fourier.HalfIntervalL2Identification
import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.ZakharovShabat.PhysicalIntervalL2

/-! # Exact unit-interval Fourier equivalence

Fourier synthesis is a complex linear isometry onto the ordinary Lebesgue
L2 class space on (0,1]. Its inverse is the actual unit Fourier integral.
Both inverse identities hold without endpoint matching or continuity.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.ZakharovShabat

/-- Synthesize the original unit-interval L2 class from its unit Fourier coefficients. -/
def unitL2SynthesisLinear : Coeff 2 →ₗ[ℂ] IntervalL2 where
  toFun a := (memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).toLp _
  map_add' a b := by
    apply Lp.ext
    filter_upwards [(memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis (a+b))).coeFn_toLp,
      (memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).coeFn_toLp,
      (memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis b)).coeFn_toLp,
      Lp.coeFn_add ((memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).toLp _)
        ((memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis b)).toLp _),
      show intervalPullback 1 (l2Synthesis (a+b)) =ᵐ[volume.restrict (Ioc 0 1)]
        intervalPullback 1 (l2Synthesis a)+intervalPullback 1 (l2Synthesis b) from by
          simpa only [map_add,Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
            intervalPullback_add (by norm_num : (0:ℝ) < 1) (l2Synthesis a) (l2Synthesis b)] with x hx ha hb hab he
    exact hx.trans (he.trans (by simp only [hab,Pi.add_apply,ha,hb]))
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [(memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis (c • a))).coeFn_toLp,
      (memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).toLp _),
      show intervalPullback 1 (l2Synthesis (c • a)) =ᵐ[volume.restrict (Ioc 0 1)]
        c • intervalPullback 1 (l2Synthesis a) from by
          simpa only [map_smul,Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
            intervalPullback_smul (by norm_num : (0:ℝ) < 1) c (l2Synthesis a)] with x hx ha hca he
    exact hx.trans (he.trans (by simp only [RingHom.id_apply,hca,Pi.smul_apply,ha]))

/-- The synthesized class has the actual dilated circle representative almost everywhere. -/
theorem unitL2SynthesisLinear_representative (a : Coeff 2) :
    unitL2SynthesisLinear a =ᵐ[volume.restrict (Ioc 0 1)] intervalPullback 1 (l2Synthesis a) :=
  (memLp_intervalPullback (by norm_num : (0:ℝ) < 1) (l2Synthesis a)).coeFn_toLp

/-- Every normalized physical unit-interval Fourier integral recovers the input coefficient. -/
theorem unitL2SynthesisLinear_coefficient (a : Coeff 2) (n : ℤ) :
    intervalFourierCoefficient 1 (unitL2SynthesisLinear a) n = a n := by
  rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),
    congrFun (fourierCoeffOn_congr_ae (by norm_num) (unitL2SynthesisLinear_representative a)) n,
    ← intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),
    intervalFourierCoefficient_intervalPullback (by norm_num),fourierCoeff_l2Synthesis]

/-- Parseval gives exact equality with the unnormalized unit-interval L2 norm. -/
theorem unitL2SynthesisLinear_norm (a : Coeff 2) : ‖unitL2SynthesisLinear a‖ = ‖a‖ := by
  have hs := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ) < 1) (Lp.memLp (unitL2SynthesisLinear a))
  simp only [← intervalFourierCoefficient_eq_fourierCoeffOn,unitL2SynthesisLinear_coefficient,
    sub_zero,inv_one,one_smul,← norm_sq_intervalL2] at hs
  have ht : HasSum (fun n => ‖a n‖^2) (‖a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a
  nlinarith [hs.unique ht,norm_nonneg (unitL2SynthesisLinear a),norm_nonneg a]

/-- The physical unit-interval Fourier synthesis is a complex linear isometry. -/
def unitL2SynthesisIsometry : Coeff 2 →ₗᵢ[ℂ] IntervalL2 :=
  ⟨unitL2SynthesisLinear,unitL2SynthesisLinear_norm⟩

/-- Every unit-interval L2 class is synthesized, without regularity or endpoint conditions. -/
theorem unitL2SynthesisIsometry_surjective : Function.Surjective unitL2SynthesisIsometry := by
  intro u
  refine ⟨unitIntervalMemLpCoefficients u (Lp.memLp u),?_⟩
  apply Lp.ext
  have h := unitL2SynthesisLinear_representative (unitIntervalMemLpCoefficients u (Lp.memLp u))
  have he : l2Synthesis (unitIntervalMemLpCoefficients u (Lp.memLp u)) =
      intervalL2Class (by norm_num : (0:ℝ) < 1) u (Lp.memLp u) := by
    exact fourierBasis.repr.symm_apply_apply _
  rw [he] at h
  exact h.trans (by simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
    intervalPullback_intervalL2Class (by norm_num : (0:ℝ) < 1) u (Lp.memLp u))

/-- The exact unit-interval Fourier equivalence in the original Hilbert norms. -/
def unitL2SynthesisEquiv : Coeff 2 ≃ₗᵢ[ℂ] IntervalL2 :=
  LinearIsometryEquiv.ofSurjective unitL2SynthesisIsometry unitL2SynthesisIsometry_surjective

/-- Actual integral coefficients reconstruct any square-integrable representative. -/
theorem unitL2SynthesisEquiv_memLpCoefficients (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    unitL2SynthesisEquiv (unitIntervalMemLpCoefficients f hf) = hf.toLp f := by
  apply Lp.ext
  have h := unitL2SynthesisLinear_representative (unitIntervalMemLpCoefficients f hf)
  have he : l2Synthesis (unitIntervalMemLpCoefficients f hf) =
      intervalL2Class (by norm_num : (0:ℝ) < 1) f hf := fourierBasis.repr.symm_apply_apply _
  rw [he] at h
  have hr : intervalPullback 1 (intervalL2Class (by norm_num : (0:ℝ) < 1) f hf)
      =ᵐ[volume.restrict (Ioc 0 1)] f := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
      intervalPullback_intervalL2Class (by norm_num : (0:ℝ) < 1) f hf
  exact h.trans (hr.trans hf.coeFn_toLp.symm)

/-- Finite coefficients reconstruct the original period-one Fourier polynomial. -/
theorem unitL2SynthesisEquiv_ofFinsupp (a : ℤ →₀ ℂ) :
    unitL2SynthesisEquiv (Coeff.ofFinsupp a) =ᵐ[volume.restrict (Ioc 0 1)] polynomial a := by
  rw [← unitIntervalMemLpCoefficients_polynomial a,unitL2SynthesisEquiv_memLpCoefficients]
  exact (memLp_two_interval (continuous_polynomial a) 0 1 (by norm_num)).coeFn_toLp

/-- The inverse equivalence is the original normalized physical Fourier integral. -/
theorem unitL2SynthesisEquiv_symm_coefficient (u : IntervalL2) (n : ℤ) :
    unitL2SynthesisEquiv.symm u n = intervalFourierCoefficient 1 u n := by
  have h := unitL2SynthesisLinear_coefficient (unitL2SynthesisEquiv.symm u) n
  change intervalFourierCoefficient 1 (unitL2SynthesisEquiv (unitL2SynthesisEquiv.symm u)) n = _ at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- Equality of all unit Fourier integrals determines an L2 class. -/
theorem unitL2_ext_coefficients (u v : IntervalL2)
    (h : ∀ n, intervalFourierCoefficient 1 u n = intervalFourierCoefficient 1 v n) : u = v := by
  apply unitL2SynthesisEquiv.symm.injective
  ext n
  simpa only [unitL2SynthesisEquiv_symm_coefficient] using h n

/-- Physical conjugation reverses the Fourier frequency on arbitrary L2 classes. -/
theorem intervalFourierCoefficient_Lp_star (u : IntervalL2) (n : ℤ) :
    intervalFourierCoefficient 1 (star u : IntervalL2) n =
      (starRingEnd ℂ) (intervalFourierCoefficient 1 u (-n)) := by
  calc
    _ = intervalFourierCoefficient 1 (fun x => (starRingEnd ℂ) (u x)) n := by
      simp only [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0:ℝ) < 1)]
      exact congrFun (fourierCoeffOn_congr_ae (by norm_num)
        (by
          filter_upwards [Lp.coeFn_star u] with x hx
          exact hx)) n
    _ = _ := intervalFourierCoefficient_conj u n

end NLS.Fourier
