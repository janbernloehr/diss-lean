import NLS.MKdV.MiuraHillPrimitiveEndpoint
import NLS.Articles.MKdVNLSHierarchies.SobolevPrimitiveIdentification

/-! # Lemmas 4 and 5 on their full original real H¹ gap complement

The canonical sheets are limits of the independent physical IVP sheets
from nonreal energies. These limits exist and are analytic across every
real band, preserve the physical trace and derivative, have the prescribed
first-band root sign, and give the actual ground-normalized path integral.
-/
noncomputable section
open Set Complex Filter Topology NLS.MKdV NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

def canonicalHillRoot (a : ScalarDomain 2) : ℂ → ℂ := canonicalMiuraHillRoot a
def canonicalHillPrimitive (a : ScalarDomain 2) : ℂ → ℂ := canonicalMiuraHillPrimitive a

theorem lemma4_root_real_H1_gapComplement (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))) :
    canonicalHillRoot a (z^2) =
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z :=
  (canonicalMiuraHillSheets_eq_NLS a ha z hzr hz).1

theorem lemma5_primitive_real_H1_gapComplement (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))) :
    canonicalHillPrimitive a (z^2) = sourceAbelianPrimitive (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property z :=
  (canonicalMiuraHillSheets_eq_NLS a ha z hzr hz).2

theorem lemma4_square_maps_gapComplements (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re) :
    z^2 ∈ miuraHillGapComplement a ha ↔
      z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) :=
  miuraHillGapComplement_sq_iff a ha z hzr

theorem canonicalHillSheets_continue_original (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    canonicalHillRoot a μ = hillRoot a μ ∧ canonicalHillPrimitive a μ = hillPrimitive a μ :=
  ⟨canonicalMiuraHillRoot_eq_original a μ ht,canonicalMiuraHillPrimitive_eq_original a μ ht⟩

theorem canonicalHillSheets_analytic (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    AnalyticOnNhd ℂ (canonicalHillRoot a) (miuraHillGapComplement a ha) ∧
      AnalyticOnNhd ℂ (canonicalHillPrimitive a) (miuraHillGapComplement a ha) :=
  analyticOnNhd_canonicalMiuraHillSheets a ha

theorem canonicalHillPrimitive_physical_trace (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    2*cosh (canonicalHillPrimitive a μ) = hillL2Discriminant (sobolevMiuraHillPotential a) μ ∧
      2*sinh (canonicalHillPrimitive a μ) = canonicalHillRoot a μ :=
  canonicalMiuraHillSheets_physical_trace a ha μ hμ

theorem canonicalHillPrimitive_hasDerivAt (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    HasDerivAt (canonicalHillPrimitive a)
      (deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) μ / canonicalHillRoot a μ) μ :=
  hasDerivAt_canonicalMiuraHillPrimitive a ha μ hμ

/-- The literal branch normalization (10) on the whole first Hill band. -/
theorem equation10_first_Hill_band (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℝ)
    (hμ : μ ∈ Ioo (miuraHillLabels a ha 0) (miuraHillLabels a ha 1)) :
    (I*canonicalHillRoot a μ).im = 0 ∧ 0 < (I*canonicalHillRoot a μ).re := by
  have hp : 0 < μ := (miuraHillLabels_nonnegative a ha 0).trans_lt hμ.1
  have hs : (Real.sqrt μ)^2 = μ := Real.sq_sqrt hp.le
  have hL1 := (miuraNLSLeft_pos a ha (show (0 : ℤ) < 1 by norm_num)).le
  have he1 : miuraHillLabels a ha 1 = (miuraNLSLeft a 1).re^2 := by
    simpa only [mul_one,show (2 : ℕ)-1 = 1 by norm_num,Nat.cast_one] using
      miuraHillLabels_left a ha 1 (by norm_num)
  have hx : Real.sqrt μ ∈ Ioo (miuraNLSRight a 0).re (miuraNLSLeft a 1).re := by
    constructor
    · apply (sq_lt_sq₀ (miuraNLSRight_zero_nonnegative a) (Real.sqrt_nonneg μ)).mp
      rw [hs,← miuraHillLabels_ground a ha]
      exact hμ.1
    · apply (sq_lt_sq₀ (Real.sqrt_nonneg μ) hL1).mp
      rw [hs,← he1]
      exact hμ.2
  have hc : ((Real.sqrt μ : ℝ) : ℂ)^2 = (μ : ℂ) := by exact_mod_cast hs
  simpa only [canonicalHillRoot,hc] using canonicalMiuraHillRoot_firstBand_sign a ha (Real.sqrt μ) hx

theorem canonicalHillPrimitive_ground_limit (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    Tendsto (canonicalHillPrimitive a)
      (𝓝[miuraHillGapComplement a ha] (miuraHillLabels a ha 0 : ℂ)) (𝓝 0) :=
  canonicalMiuraHillPrimitive_ground_limit a ha

/-- Equation (11) uses the actual physical L² Hill discriminant. -/
theorem equation11_physical_Hill_pathIntegral (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) {μ : ℂ}
    (γ : Path (miuraHillLabels a ha 0 : ℂ) μ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ miuraHillGapComplement a ha)
    (hμ : μ ∈ miuraHillGapComplement a ha)
    (hint : CurveIntegrable (holomorphicOneForm (fun w =>
      deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) w / canonicalHillRoot a w)) γ) :
    (∫ᶜ w in γ, holomorphicOneForm (fun w =>
      deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) w / canonicalHillRoot a w) w) =
        canonicalHillPrimitive a μ :=
  canonicalMiuraHillPrimitive_eq_pathIntegral a ha γ hγ hγs hμ hint

end NLS.Articles.MKdVNLSHierarchies
