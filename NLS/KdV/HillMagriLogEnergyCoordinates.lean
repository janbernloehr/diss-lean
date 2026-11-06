import NLS.KdV.HillLogNormingMagriBrackets
import NLS.KdV.HillWeakMagriScalars
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Independent logarithmic-energy separated coordinates for the Magri bracket

The actual derivative of (1/2) log(mu_n) rescales the Dirichlet gradient
by (2 mu_n)^(-1). Its mixed weak Magri bracket with the independently
constructed log-norming coordinate is -delta. This is a spectral
separated-coordinate calculation; it is not a construction of the final
mKdV Abelian angle.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillLogEnergyGradientCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) : Curve ℂ :=
  (2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))⁻¹ • hillDirichletGradientCurve q n hn

def hillLogEnergyGradientSpatialCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) : Curve ℂ :=
  (2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))⁻¹ • hillDirichletGradientSpatialCurve q n hn

def hillLogEnergyGradientSecond (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : ℂ :=
  (2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))⁻¹*hillDirichletGradientSecond q n hn x

theorem hillLogEnergy_branch_fderiv (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hpos : 0 < hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val) = (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p) = 0)
    (h : Coeff 2) :
    fderiv ℂ (fun p => (1/2 : ℂ)*Complex.log (a p)) (SpectralWeight.one.toCoeff q.val) h =
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*extend (hillLogEnergyGradientCurve q n hn) x := by
  have hslit : a (SpectralWeight.one.toCoeff q.val) ∈ Complex.slitPlane := by
    rw [ha0]
    exact mem_slitPlane_iff.mpr (Or.inl (by simpa only [ofReal_re] using hpos))
  have hd := ((Complex.hasDerivAt_log hslit).comp_hasFDerivAt _ ha.differentiableAt.hasFDerivAt).const_smul (1/2 : ℂ)
  change HasFDerivAt (fun p => (1/2 : ℂ)*Complex.log (a p)) _ _ at hd
  rw [hd.fderiv]
  change (1/2 : ℂ)*((a (SpectralWeight.one.toCoeff q.val))⁻¹*
    (fderiv ℂ a (SpectralWeight.one.toCoeff q.val) h)) = _
  rw [ha0,hillDirichletGradient_represents_branch q n hn a ha ha0 hz h]
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  have he : (1/2 : ℂ)*mu⁻¹ = (2*mu)⁻¹ := by rw [mul_inv_rev]; ring
  rw [← mul_assoc,he,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change (2*mu)⁻¹*(-(hillPhysicalDirection h).ofLp.2 x*extend (hillDirichletGradientCurve q n hn) x) =
    -(hillPhysicalDirection h).ofLp.2 x*((2*mu)⁻¹*extend (hillDirichletGradientCurve q n hn) x)
  ring

theorem hillLogEnergyLogNormingMagriBracket_eq (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hmu : hillDirichletEnergy q.val q.property.1 q.property.2 n hn ≠ 0) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogEnergyGradientCurve q n hn)
      (hillLogEnergyGradientSpatialCurve q n hn) (hillLogEnergyGradientSecond q n hn)
      (hillLogNormingGradientCurve q m hm) (hillLogNormingGradientSpatialCurve q m hm) =
        if n = m then -1 else 0 := by
  dsimp only [hillLogEnergyGradientCurve,hillLogEnergyGradientSpatialCurve,hillLogEnergyGradientSecond]
  rw [show hillLogEnergyGradientSecond q n hn = (fun x =>
    (2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))⁻¹*hillDirichletGradientSecond q n hn x) from rfl,
    hillWeakGradientMagri_smul_left]
  change _*hillDirichletLogMagriBracket q n m hn hm = _
  rw [hillDirichletLogMagriBracket_eq]
  by_cases he : n = m
  · rw [if_pos he,if_pos he]
    have hmuc : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ≠ 0 := ofReal_ne_zero.mpr hmu
    field_simp [hmuc]
  · rw [if_neg he,if_neg he,mul_zero]

theorem hillLogEnergyMagriBracket_eq_zero (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogEnergyGradientCurve q n hn)
      (hillLogEnergyGradientSpatialCurve q n hn) (hillLogEnergyGradientSecond q n hn)
      (hillLogEnergyGradientCurve q m hm) (hillLogEnergyGradientSpatialCurve q m hm) = 0 := by
  dsimp only [hillLogEnergyGradientCurve,hillLogEnergyGradientSpatialCurve,hillLogEnergyGradientSecond]
  rw [show hillLogEnergyGradientSecond q n hn = (fun x =>
    (2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))⁻¹*hillDirichletGradientSecond q n hn x) from rfl,
    hillWeakGradientMagri_smul_left,hillWeakGradientMagri_smul_right]
  change _*(_*hillDirichletMagriBracket q n m hn hm) = 0
  rw [hillDirichletMagriBracket_eq_zero,mul_zero,mul_zero]

end NLS.KdV
