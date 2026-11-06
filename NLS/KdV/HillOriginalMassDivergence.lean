import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.Fourier.PeriodTwoRestriction
import NLS.SequenceSpaces.NonnegativeEnergyDivergence
import NLS.SequenceSpaces.SobolevDerivative

/-! # Divergence of original physical L2 mass at genuinely rough source limits

The original source map samples the even period-two Fourier modes. Its
contractive sampling bound proves divergence for every family of original
L2 approximants, without any spectral chart or finite-gap assumption.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Every ORIGINAL L2 approximation of a genuinely non-L2 rough source
has diverging squared L2 norm, for any filter of approximants. -/
theorem tendsto_original_L2_norm_sq_atTop_of_nonL2_hminus_limit
    {ι : Type*} {l : Filter ι} (q : PeriodOneHminusOne) (hq : ¬ Memℓp q.val 2)
    (a : ι → WeightedCoeff SpectralWeight.one.toWeight 2)
    (ht : Tendsto (fun i => hillOriginalHminusSource (a i)) l (𝓝 q)) :
    Tendsto (fun i => ‖a i‖^2) l atTop := by
  let u (i : ι) : Coeff 2 := Fourier.paritySample 0 (SpectralWeight.one.toCoeff (a i))
  have hnot : ¬ Summable (fun j : ℤ => ‖q.val j‖^2) := by
    intro hs
    apply hq
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs
  apply tendsto_atTop_of_nonsummable_coordinate_limit (fun j : ℤ => ‖q.val j‖^2)
    (fun j => sq_nonneg _) hnot (fun i j => ‖u i j‖^2) (fun i => ‖a i‖^2)
  · intro j
    have h := ((WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 j).continuous.tendsto q).comp ht
    have he (i : ι) : u i j=(hillOriginalHminusSource (a i)).val j := by
      rw [hillOriginalHminusSource_apply]
      simp only [u,Fourier.paritySample_apply,add_zero,SpectralWeight.toCoeff_apply]
    simpa only [he,Function.comp_def,WeightedCoeff.evalCLM_apply] using h.norm.pow 2
  · intro i S
    have hs : Summable (fun j : ℤ => ‖u i j‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.memℓp (u i)).summable (by norm_num : 0<(2 : ℝ≥0∞).toReal)
    have hsum : (∑' j : ℤ, ‖u i j‖^2)=‖u i‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) (u i)).symm
    have hn : ‖u i‖≤‖a i‖ :=
      (Fourier.norm_paritySample_le _ _).trans (SpectralWeight.norm_toCoeff_le _ _)
    calc
      ∑ j∈S, ‖u i j‖^2 ≤ ∑' j : ℤ, ‖u i j‖^2 := hs.sum_le_tsum S (fun _ _ => sq_nonneg _)
      _ = ‖u i‖^2 := hsum
      _ ≤ ‖a i‖^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The physical quadratic mass has the exact factor one half. -/
theorem tendsto_original_half_L2_norm_sq_atTop_of_nonL2_hminus_limit
    {ι : Type*} {l : Filter ι} (q : PeriodOneHminusOne) (hq : ¬ Memℓp q.val 2)
    (a : ι → WeightedCoeff SpectralWeight.one.toWeight 2)
    (ht : Tendsto (fun i => hillOriginalHminusSource (a i)) l (𝓝 q)) :
    Tendsto (fun i => (1/2 : ℝ)*‖a i‖^2) l atTop :=
  (tendsto_original_L2_norm_sq_atTop_of_nonL2_hminus_limit q hq a ht).const_mul_atTop
    (by norm_num)

/-- Native H^s convergence, for every s ≥ -1, implies divergence of the
original physical L2 mass. The raw coefficient identity fixes the source
normalization and the topology is the actual weighted Hilbert topology. -/
theorem tendsto_original_half_L2_norm_sq_atTop_of_nonL2_sobolev_limit
    {ι : Type*} {l : Filter ι} {s : ℝ} (hs : -1 ≤ s)
    (q : WeightedCoeff (Weight.sobolev s) 2) (hq : ¬ Memℓp q.val 2)
    (a : ι → WeightedCoeff SpectralWeight.one.toWeight 2)
    (v : ι → WeightedCoeff (Weight.sobolev s) 2)
    (hv : ∀ i j, (v i).val j=(a i).val (2*j))
    (ht : Tendsto v l (𝓝 q)) :
    Tendsto (fun i => (1/2 : ℝ)*‖a i‖^2) l atTop := by
  let q' : PeriodOneHminusOne := WeightedCoeff.sobolevInclusion hs q
  have hq' : ¬ Memℓp q'.val 2 := by
    have heq : q'.val=q.val := funext (fun j => WeightedCoeff.sobolevInclusion_apply hs q j)
    rwa [heq]
  apply tendsto_original_half_L2_norm_sq_atTop_of_nonL2_hminus_limit q' hq' a
  have he (i : ι) : hillOriginalHminusSource (a i)=
      WeightedCoeff.sobolevInclusion hs (v i) := by
    apply Subtype.ext
    funext j
    rw [hillOriginalHminusSource_apply, WeightedCoeff.sobolevInclusion_apply, hv]
  change Tendsto (fun i => hillOriginalHminusSource (a i)) l
    (𝓝 (WeightedCoeff.sobolevInclusion hs q))
  simpa only [he, Function.comp_def] using
    ((WeightedCoeff.sobolevInclusion hs).continuous.tendsto q).comp ht

end NLS.KdV
