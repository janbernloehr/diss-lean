import NLS.KdV.HillHminusActionRotationDifferentials
import NLS.KdV.HillHminusEndpointConjugateCommutation

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The conjugate ORIGINAL Cartesian germ has the opposite action
rotation under the SAME genuine H-minus-one Gardner bracket. -/
theorem hillOriginalConjugateCartesian_action_hminus_Gardner_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (C J : PeriodOneHminusOne → ℂ)
    (hC : AnalyticAt ℂ C (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hCM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 m 0 : ℂ)) :
    NLS.Poisson.hminusGardnerBracket C J (hillOriginalHminusSource q.val) =
      -I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ) *
        conj (hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos) := by
  obtain ⟨Z,hZ,hZM⟩ := exists_hillOriginal_cartesian_hminus_physical_germ q n hgap
  obtain ⟨A,B,hA,_,hAM,_,_,_⟩ := exists_hillOriginal_action_amplitude_hminus_differentials q n hgap
  let a := hillOriginalHminusSource q.val
  have hprod := hillOriginalCartesian_conjugate_product_fderiv q n Z C A hZ hC hA hZM hCM hAM
  have hcomm := hillOriginalActions_hminus_Gardner_commute q n m A J hA hJ hAM hJM
  have hzero : NLS.Poisson.hminusGardnerBracket (fun b => Z b * C b) J a = 0 := by
    rw [NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_left _ A J a 2 hprod,hcomm,mul_zero]
  rw [NLS.Poisson.hminusGardnerBracket_mul_left Z C J a hZ.differentiableAt hC.differentiableAt,
    hillOriginalCartesian_action_hminus_Gardner_eq q n m Z J hZ hJ hZM hJM] at hzero
  have hZn : Z a ≠ 0 := by
    rw [hZM.self_of_nhds]
    exact hillSpectralCartesian_ne_zero_open q n hgap
  rw [←hCM.self_of_nhds]
  apply mul_left_cancel₀ hZn
  rw [←hZM.self_of_nhds] at hzero
  linear_combination hzero

/-- The conjugate action rotation is an identity of ENTIRE H-minus-one
differentials, derived from ORIGINAL L2 neighborhood matching. -/
theorem hillOriginalConjugateCartesian_action_hminus_Gardner_fderiv
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (C J : PeriodOneHminusOne → ℂ)
    (hC : AnalyticAt ℂ C (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hCM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 m 0 : ℂ)) :
    fderiv ℂ (NLS.Poisson.hminusGardnerBracket C J) (hillOriginalHminusSource q.val) =
      (-I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ)) •
        fderiv ℂ C (hillOriginalHminusSource q.val) := by
  let c : ℂ := -I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ)
  have hNC := hillHminusPhysicalGerm_eventually_matching_germs q C _ hC hCM
  have hNJ := hillHminusPhysicalGerm_eventually_matching_germs q J _ hJ hJM
  have hNGap : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      hillRealGapHalfLength p.val p.property.1 p.property.2 n ≠ 0 :=
    (continuous_hillRealGapHalfLength n).continuousAt.eventually_ne hgap
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket C J) (hillOriginalHminusSource q.val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hC.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hJ.fderiv)
  have hreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      NLS.Poisson.hminusGardnerBracket C J (hillOriginalHminusSource p.val) =
        c * C (hillOriginalHminusSource p.val) := by
    filter_upwards [hNC,hNJ,hCM,hNGap] with p hpC hpJ hp hg
    rw [hillOriginalConjugateCartesian_action_hminus_Gardner_eq p n m hg C J hpC.1 hpJ.1 hpC.2 hpJ.2,hp]
  have he := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q
    (NLS.Poisson.hminusGardnerBracket C J) (fun a => c * C a) hB (analyticAt_const.mul hC) hreal
  rw [he]
  exact (hC.differentiableAt.hasFDerivAt.const_mul c).fderiv

end NLS.KdV
