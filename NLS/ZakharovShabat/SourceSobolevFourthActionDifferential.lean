import NLS.ZakharovShabat.SourceSobolevFourthActionDerivatives
import NLS.ZakharovShabat.SourceActionFiniteGapDifferential

/-! # Original weighted H₄ actions and their full finite-gap differential

The actual native action sequence takes values in ell^(3,1). Evaluation of
its real derivative is the original complex action differential on the same
raw source direction. At finite gaps a single finite cutoff supports every
direction, including variations that open a closed action.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The original physical action sequence on the native fractional source. -/
def nativeFourthActions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) : FourthSobolevActions :=
  fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)

theorem analyticAt_nativeFourthActions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) : AnalyticAt ℝ D.nativeFourthActions a :=
  (analyticOnNhd_fourthSobolevActions _ (mem_univ _)).comp
    (D.originalWeightedRealMap_analytic fourthSobolevSpectralWeight a (mem_univ _))

/-- Coordinate evaluation of the full native action differential is the
original complex source cotangent, with the unchanged physical normalization. -/
theorem nativeFourthActions_fderiv_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a h : NativeFourthSobolevSource) (n : ℤ) :
    (fderiv ℝ D.nativeFourthActions a h).val n =
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
          ((originalWeightedRealSource fourthSobolevSpectralWeight h).val) := by
  let e := (WeightedCoeff.evalCLM (p := 1) fourthSobolevActionWeight n).restrictScalars ℝ
  let L : NativeFourthSobolevSource →L[ℝ] CoeffPair 2 :=
    ((originalWeightedSourceCLM (p := 2) fourthSobolevSpectralWeight).restrictScalars ℝ).comp
      (weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight).subtypeL
  have hl := e.hasFDerivAt.comp a (D.analyticAt_nativeFourthActions a).differentiableAt.hasFDerivAt
  have hr := ((analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) n
    (L a) (originalWeightedRealSource fourthSobolevSpectralWeight a).property).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a L.hasFDerivAt
  have he : (fun b : NativeFourthSobolevSource => e (D.nativeFourthActions b)) =
      fun b => sourceComplexAction (by simp) (by norm_num) n (L b) :=
    funext fun b => D.fourthSobolevActions_realMap_eq_complexAction b n
  change HasFDerivAt (fun b => e (D.nativeFourthActions b)) _ a at hl
  rw [he] at hl
  exact congrArg (fun M => M h) (hl.unique hr)

/-- A finite cutoff supporting the original action cotangents supports the
entire native weighted sequence derivative, for every native real direction. -/
theorem nativeFourthActions_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0)
    (h : NativeFourthSobolevSource) :
    fderiv ℝ D.nativeFourthActions a h =
      ∑ n ∈ S, ((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
          (originalWeightedRealSource fourthSobolevSpectralWeight h).val) • fourthSobolevActionDirection n := by
  classical
  apply Subtype.ext
  funext k
  rw [D.nativeFourthActions_fderiv_apply]
  change _ = (WeightedCoeff.evalCLM (p := 1) fourthSobolevActionWeight k) _
  rw [map_sum]
  by_cases hk : k ∈ S
  · simp [fourthSobolevActionDirection,
      WeightedCoeff.evalCLM_apply,WeightedCoeff.single_val,Pi.single_apply,hk]
  · simp [fourthSobolevActionDirection,
      WeightedCoeff.evalCLM_apply,WeightedCoeff.single_val,Pi.single_apply,hk,hS k hk]

/-- The actual physical H₄ differential on every native real direction is
the finite sum of original action cotangents weighted by the independently
defined physical frequencies. A single cutoff works for every direction. -/
theorem sourceSobolevFourthHamiltonian_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0)
    (h : NativeFourthSobolevSource) :
    fderiv ℝ sourceSobolevFourthHamiltonian a h =
      ∑ n ∈ S, D.sobolevFourthFrequency a n *
        ((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
            (originalWeightedRealSource fourthSobolevSpectralWeight h).val) := by
  obtain ⟨V,T,H,hV,ha,hT,hmap,hH,hrec,hfreq⟩ := D.exists_sobolevFourth_action_factor_with_frequencies a
  have he : (fun b : NativeFourthSobolevSource => H (D.nativeFourthActions b)) =ᶠ[𝓝 a]
      sourceSobolevFourthHamiltonian := by
    filter_upwards [(D.originalWeightedRealMap_continuous fourthSobolevSpectralWeight).continuousAt.tendsto.eventually
      (hV.mem_nhds ha)] with b hb
    exact (hrec _ hb).trans (D.sobolevFourthBirkhoffHamiltonian_map b)
  have hd := ((hH _ (hmap ha)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a
    (D.analyticAt_nativeFourthActions a).differentiableAt.hasFDerivAt
  change HasFDerivAt (fun b => H (D.nativeFourthActions b)) _ a at hd
  rw [← he.fderiv_eq,hd.fderiv]
  change (fderiv ℂ H (D.nativeFourthActions a)) (fderiv ℝ D.nativeFourthActions a h) = _
  rw [D.nativeFourthActions_fderiv_eq_finite_sum a S hS h,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul,smul_eq_mul,nativeFourthActions,← hfreq a ha n,mul_comm]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
