import NLS.KdV.HillOnIndexRegularBranchSystem
import NLS.KdV.HillAbelianNativeEnergyEquation
import NLS.ComplexAnalysis.AnalyticBranchSystemUniqueness

/-! The even/odd ACTUAL diagonal Cartesian coefficients satisfy ONE
intrinsic branch system in ORIGINAL Hill energy. Finite analytic order
extends the equations through ALL branch points and complex collapse. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem onIndexEnergy_branch_system_of_radicand_ne_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (E : ℂ) (ht : (E,q) ∈ P.abelianFilledEnergyDomain n)
    (hne : hillHminusRadicand q E ≠ 0) :
    deriv (fun e => P.onIndexEnergyEven n (e,q)) E = (I*hillHminusCanonicalPsi n (E,q))*P.onIndexEnergyOdd n (E,q) ∧
      hillHminusRadicand q E*deriv (fun e => P.onIndexEnergyOdd n (e,q)) E+
        (deriv (hillHminusRadicand q) E/2)*P.onIndexEnergyOdd n (E,q) = (I*hillHminusCanonicalPsi n (E,q))*P.onIndexEnergyEven n (E,q) := by
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let z := Complex.sqrt (E+c)
  have hz : 0 < z.re := principal_sqrt_re_pos_of_slit (E+c) ht.1
  have he : z^2-c = E := by dsimp only [z]; rw [complex_sqrt_sq]; ring
  have hq : q ∈ P.source := ht.2.2
  have hdisc : z ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := ht.2.1
  have hQ : sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z ≠ 0 := by
    intro hzero
    have hp := P.abelianGapRootMultiplier_sq_mul_polynomial n (z,q) ⟨hdisc,hq⟩
    rw [hzero,mul_zero,he] at hp
    exact hne hp.symm
  have hs := P.onIndexFrequency_branch_system_of_quadratic_ne_zero n q hq z hdisc hQ
  let A : ℂ → ℂ := fun e => P.onIndexEnergyEven n (e,q)
  let B : ℂ → ℂ := fun e => P.onIndexEnergyOdd n (e,q)
  have hA : AnalyticAt ℂ A E := (P.analytic_onIndexEnergyEven n (E,q) ht).comp
    (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticAt ℂ B E := (P.analytic_onIndexEnergyOdd n (E,q) ht).comp
    (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticAt ℂ (hillHminusRadicand q) E := analyticOnNhd_hillHminusRadicand q E (mem_univ _)
  have hsquare : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one,mul_one] using
      (((hasDerivAt_id z).pow 2).sub_const c)
  have hAd : HasDerivAt A (deriv A E) (z^2-c) := he.symm ▸ hA.differentiableAt.hasDerivAt
  have hBd : HasDerivAt B (deriv B E) (z^2-c) := he.symm ▸ hB.differentiableAt.hasDerivAt
  have hDd : HasDerivAt (hillHminusRadicand q) (deriv (hillHminusRadicand q) E) (z^2-c) := he.symm ▸ hD.differentiableAt.hasDerivAt
  have hdA := hAd.comp z hsquare
  have hdB := hBd.comp z hsquare
  have hdD := hDd.comp z hsquare
  change HasDerivAt (fun w => A (w^2-c)) _ z at hdA
  change HasDerivAt (fun w => B (w^2-c)) _ z at hdB
  change HasDerivAt (fun w => hillHminusRadicand q (w^2-c)) _ z at hdD
  have hnearA : (fun w => P.onIndexFrequencyEven n (w,q)) =ᶠ[𝓝 z] (fun w => A (w^2-c)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (P.onIndexEnergyCoefficients_at_positive_frequency n q w hw).1.symm
  have hnearB : (fun w => P.onIndexFrequencyOdd n (w,q)) =ᶠ[𝓝 z] (fun w => B (w^2-c)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (P.onIndexEnergyCoefficients_at_positive_frequency n q w hw).2.symm
  have hvalA : P.onIndexFrequencyEven n (z,q) = A E := by simpa only [he] using hnearA.eq_of_nhds
  have hvalB : P.onIndexFrequencyOdd n (z,q) = B E := by simpa only [he] using hnearB.eq_of_nhds
  rw [hnearA.deriv_eq,hdA.deriv,hnearB.deriv_eq,hdB.deriv,hdD.deriv,hvalA,hvalB] at hs
  change deriv A E*(2*z) = (I*(2*z*hillHminusCanonicalPsi n (z^2-c,q)))*B E ∧
    hillHminusRadicand q (z^2-c)*(deriv B E*(2*z))+
      ((deriv (hillHminusRadicand q) E*(2*z))/2)*B E = (I*(2*z*hillHminusCanonicalPsi n (z^2-c,q)))*A E at hs
  rw [he] at hs
  have hzn : z ≠ 0 := by intro hzero; rw [hzero,zero_re] at hz; exact lt_irrefl 0 hz
  have h2z := mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hzn
  constructor
  · apply mul_left_cancel₀ h2z
    linear_combination hs.1
  · apply mul_left_cancel₀ h2z
    linear_combination hs.2

theorem onIndexEnergy_branch_system (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (E : ℂ) (ht : (E,q) ∈ P.abelianFilledEnergyDomain n) :
    deriv (fun e => P.onIndexEnergyEven n (e,q)) E = (I*hillHminusCanonicalPsi n (E,q))*P.onIndexEnergyOdd n (E,q) ∧
      hillHminusRadicand q E*deriv (fun e => P.onIndexEnergyOdd n (e,q)) E+
        (deriv (hillHminusRadicand q) E/2)*P.onIndexEnergyOdd n (E,q) = (I*hillHminusCanonicalPsi n (E,q))*P.onIndexEnergyEven n (E,q) := by
  let Ω := {e : ℂ | (e,q) ∈ P.abelianFilledEnergyDomain n}
  have hΩ : IsOpen Ω := (P.abelianFilledEnergyDomain_open n).preimage (continuous_id.prodMk continuous_const)
  have hA : AnalyticOnNhd ℂ (fun e => P.onIndexEnergyEven n (e,q)) Ω := by
    intro e he
    exact (P.analytic_onIndexEnergyEven n (e,q) he).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticOnNhd ℂ (fun e => P.onIndexEnergyOdd n (e,q)) Ω := by
    intro e he
    exact (P.analytic_onIndexEnergyOdd n (e,q) he).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hD := analyticOnNhd_hillHminusRadicand q
  have hΨ : AnalyticAt ℂ (fun e => hillHminusCanonicalPsi n (e,q)) E :=
    (analyticOnNhd_hillHminusCanonicalPsi n (E,q) ⟨mem_univ _,mem_iUnion.mpr ⟨P.parent,P.subset ht.2.2⟩⟩).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  let F : ℂ → ℂ × ℂ := fun e =>
    (deriv (fun w => P.onIndexEnergyEven n (w,q)) e-(I*hillHminusCanonicalPsi n (e,q))*P.onIndexEnergyOdd n (e,q),
      hillHminusRadicand q e*deriv (fun w => P.onIndexEnergyOdd n (w,q)) e+
        (deriv (hillHminusRadicand q) e/2)*P.onIndexEnergyOdd n (e,q)-(I*hillHminusCanonicalPsi n (e,q))*P.onIndexEnergyEven n (e,q))
  have hF : ContinuousAt F E := by
    have hAe := hA E ht
    have hBe := hB E ht
    have hDe := hD E (mem_univ _)
    exact ((hAe.deriv.sub ((analyticAt_const.mul hΨ).mul hBe)).continuousAt).prodMk
      ((((hDe.mul hBe.deriv).add (hDe.deriv.div_const.mul hBe)).sub ((analyticAt_const.mul hΨ).mul hAe)).continuousAt)
  have hfinite : analyticOrderAt (hillHminusRadicand q) E ≠ ⊤ := by
    obtain ⟨N,V,_,_,hqV,hcontrol⟩ := exists_hillHminus_central_controls q
    have hc := hcontrol N le_rfl q hqV
    exact analyticOrderAt_ne_top_on_connected isPreconnected_univ hD (mem_univ _)
      (hc.separator_ne_zero (hillCentralSeparator N:ℂ) rfl) (mem_univ E)
  have hzero : F E = 0 := continuousAt_zero_of_off_analytic_zeros (hillHminusRadicand q) F E (hD E (mem_univ _)) hfinite hF (by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ e in 𝓝 E, e ∈ Ω from hΩ.mem_nhds ht)] with e he hne
    have hs := P.onIndexEnergy_branch_system_of_radicand_ne_zero n q e he hne
    exact Prod.ext (sub_eq_zero.mpr hs.1) (sub_eq_zero.mpr hs.2))
  exact ⟨sub_eq_zero.mp (congrArg Prod.fst hzero),sub_eq_zero.mp (congrArg Prod.snd hzero)⟩

end NLS.KdV.HillProductEquationPatch
