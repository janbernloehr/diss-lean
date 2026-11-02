import NLS.MKdV.MiuraHillSpectralBridge
import NLS.KdV.HillNLSPrimitivePathComparison
import NLS.ZakharovShabat.ContinuousPotentialSource

/-! # The actual free-normalized Miura Hill and diagonal NLS primitives

The source path is s*u. Its Hill image is s*u' + s²*u², rather than the
straight segment s*(u'+u²). Both actual constructions are continuous on
this real path. Physical trace equality and the free values fix the root
and the primitive, without an undetermined sign or logarithm period.
-/
noncomputable section
open scoped ComplexConjugate
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open NLS.FunctionalAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ContDiff ENNReal
namespace NLS.MKdV

def realDiagonalProfileSource (u : ℝ → ℂ) (hu : Continuous u)
    (hr : ∀ x, (u x).im = 0) : realTypeSourceSubmodule 2 :=
  ⟨continuousPotentialSource (classicalPotentialOfFunctions u u hu hu),
    continuousPotentialSource_realType _ (fun t => (conj_eq_iff_im.mpr (hr t)).symm)⟩

def miuraScaledHillProfileCurve (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (s : ℝ) : Curve ℂ :=
  (s : ℂ) • miuraProfileCurve (deriv u) (hu.continuous_deriv (by norm_num)) +
    (s : ℂ)^2 • (miuraProfileCurve u hu.continuous)^2

theorem continuous_miuraScaledHillProfileCurve (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) :
    Continuous (miuraScaledHillProfileCurve u hu) := by
  unfold miuraScaledHillProfileCurve
  fun_prop

theorem miuraScaledHillProfileCurve_eq (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (s : ℝ) :
    miuraScaledHillProfileCurve u hu s =
      miuraHillProfileCurve (fun x => (s : ℂ)*u x) (contDiff_const.mul hu) := by
  ext t
  change (s : ℂ)*deriv u t+(s : ℂ)^2*u t^2 =
    deriv (fun x => (s : ℂ)*u x) t+((s : ℂ)*u t)^2
  rw [((hu.differentiable (by norm_num) t).hasDerivAt.const_mul (s : ℂ)).deriv]
  ring

theorem miuraScaledHillProfileCurve_real (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hr : ∀ x, (u x).im = 0) (s : ℝ) (t : Icc (0 : ℝ) 1) :
    (miuraScaledHillProfileCurve u hu s t).im = 0 := by
  have hd : (deriv u t).im = 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (t : ℝ)
      (hu.differentiable (by norm_num) t).hasDerivAt
    have he : (fun x => (u x).im) = fun _ => (0 : ℝ) := funext hr
    change HasDerivAt (fun x => (u x).im) (deriv u t).im (t : ℝ) at h
    rw [he] at h
    simpa only [deriv_const] using h.deriv.symm
  change ((s : ℂ)*deriv u t+(s : ℂ)^2*u t^2).im = 0
  simp only [pow_two,add_im,mul_im,ofReal_im,ofReal_re,hr t,hd,mul_zero,
    zero_mul,add_zero]

/-- The actual spectral root and primitive agree on the nonreal part of
the right frequency half-plane for every real C¹ periodic profile.
The source on the NLS side is its original physical Fourier realization. -/
theorem miuraHill_sheets_eq_NLS (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hr : ∀ x, (u x).im = 0) (hp : Function.Periodic u 1)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    classicalHillContinuedRoot (z^2,miuraHillProfileCurve u hu) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalProfileSource u hu.continuous hr).val z ∧
    classicalHillContinuedPrimitive (z^2,miuraHillProfileCurve u hu) =
      sourceAbelianPrimitive (by simp) (by norm_num) (realDiagonalProfileSource u hu.continuous hr).val
        (realDiagonalProfileSource u hu.continuous hr).property z := by
  let φ := realDiagonalProfileSource u hu.continuous hr
  let ψ : ℝ → realTypeSourceSubmodule 2 := fun s => s • φ
  let q := miuraScaledHillProfileCurve u hu
  have hψ : Continuous ψ := by fun_prop
  have hψ0 : ψ 0 = 0 := zero_smul ℝ φ
  have hq0 : q 0 = 0 := by
    ext t
    change (0 : ℂ)*deriv u t+(0 : ℂ)^2*u t^2 = 0
    ring
  have hqr (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) (t : Icc (0 : ℝ) 1) :
      (q s t).im = 0 := miuraScaledHillProfileCurve_real u hu hr s t
  have htrace (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
      classicalHillDiscriminant (q s) (z^2) =
        canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z := by
    rw [show q s = miuraHillProfileCurve (fun x => (s : ℂ)*u x) (contDiff_const.mul hu) from
      miuraScaledHillProfileCurve_eq u hu s]
    rw [classicalHillDiscriminant_miura_eq_ZS _ _ (by intro x; exact congrArg (fun a : ℂ => (s : ℂ)*a) (hp x))]
    change _ = canonicalDiscriminant (by simp)
      (periodOnePotential ((s : ℂ) • continuousPotentialSource
        (classicalPotentialOfFunctions u u hu.continuous hu.continuous))) z
    rw [← map_smul,canonicalDiscriminant_continuousPotentialSource]
    congr 1
  have he : q 1 = miuraHillProfileCurve u hu := by
    ext t
    change (1 : ℂ)*deriv u t+(1 : ℂ)^2*u t^2 = deriv u t+u t^2
    ring
  have hψ1 : ψ 1 = φ := one_smul ℝ φ
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hroot := classicalHillContinuedRoot_eq_NLS_along_path ψ hψ hψ0 q
    (continuous_miuraScaledHillProfileCurve u hu) hq0 hqr z hzr hzi htrace ht
  have hprimitive := classicalHillContinuedPrimitive_eq_NLS_along_path ψ hψ hψ0 q
    (continuous_miuraScaledHillProfileCurve u hu) hq0 hqr z hzr hzi htrace ht
  dsimp only at hroot hprimitive
  rw [he,hψ1] at hroot hprimitive
  exact ⟨hroot,hprimitive⟩

end NLS.MKdV
