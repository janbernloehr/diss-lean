import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ZakharovShabat.SourceAngularEtaCauchyEquation
import NLS.ZakharovShabat.SourceAngularEtaRemainderChoiceIndependence

/-!
# Eta remainder sheet primitives constructed by Cauchy projection

Multiplication by the canonical or selected sheet root gives the actual
eta remainder primitive. Both endpoint limits are zero. The construction
uses the midpoint and squared gap, so it also applies at collapsed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

theorem eta_cauchy_sheet_primitive_data
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (w : ℂ) (hw : w ≠ 0) :
    let H : ℂ → ℂ := fun z => sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)
    let F : ℂ → ℂ := fun z => sourceStandardRoot hp hp1 ψ m z*H z
    let E : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ) /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)*H z
    SourceAngularEtaRemainderSheetPrimitiveData hp hp1 m s ψ (c m) r w F E := by
  dsimp only
  let H : ℂ → ℂ := fun z => sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)
  let Q := sourceStandardRoot hp hp1 ψ m
  let K : ℂ → ℂ := fun z => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z
  let S : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ)
  let B : ℂ → ℂ := fun z => S z/K z
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let d := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2/4
  let Ω := ball (c m) r
  let Λ := sourceAngularRegularSheetDisc hp ψ (c m) r w
  let X := Ω \ sourcePeriodicSegment hp hp1 ψ m
  have hΩρ : Ω ⊆ ball (c m) ρ := ball_subset_ball hrρ.le
  have hΩT : Ω ⊆ ball (c m) (T m) :=
    ball_subset_ball (D.inner_lt_outer.trans D.outer_lt_assigned).le
  have hother (z : ℂ) (hz : z ∈ Ω) : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    ((D.disc_family ψ hψ).contour_family.2 m).2.2.1 (ball_subset_closedBall (hΩT hz))
  have hK : AnalyticOnNhd ℂ K Ω := by
    intro z hz
    exact analyticAt_const.mul ((D.omitted_analytic (z,ψ) ⟨hΩT hz,hψ⟩).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const))
  have hKne (z : ℂ) (hz : z ∈ Ω) : K z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hother z hz))
  have hH : AnalyticOnNhd ℂ H Ω := by
    intro z hz
    exact (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR (z,ψ) ⟨hΩρ hz,hψ⟩).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticOnNhd ℂ B Λ := by
    intro z hz
    exact ((analyticOnNhd_sourceAngularRootSheet hp hp1 w (z,ψ) hz.2).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)).div
      (hK z hz.1) (hKne z hz.1)
  have hBne (z : ℂ) (hz : z ∈ Λ) : B z ≠ 0 :=
    div_ne_zero (sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.2) (hKne z hz.1)
  have hBsq (z : ℂ) (hz : z ∈ Ω) : B z^2 = quadraticRootPolynomial τ d z := by
    rw [show quadraticRootPolynomial τ d z = sourceAngularSelectedPolynomial hp hp1 ψ m z from rfl,
      sourceAngularSelectedPolynomial_eq_endpoint_factor]
    dsimp only [B,S,K]
    rw [div_pow,sourceAngularRootSheet_sq hp w hw]
    dsimp only [sourceAngularRadicand]
    rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m z,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m z (hother z hz),
      mul_pow,mul_pow,I_sq]
    have hPne := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hother z hz)
    field_simp
    ring
  have hQsq (z : ℂ) (hz : z ∈ X) : Q z^2 = quadraticRootPolynomial τ d z :=
    (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z hz.2).trans
      (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ m z).symm
  have heq (z : ℂ) (hz : z ∈ Ω) :
      quadraticRootPolynomial τ d z*deriv H z+(z-τ)*H z = sourceAngularGapNumerator hp hp1 m m s ψ z-I :=
    D.etaQuotientCauchyCandidate_equation ψ hψ ρ hrρ hρR z (hΩρ hz)
  have hFd (z : ℂ) (hz : z ∈ X) : HasDerivAt (fun z => Q z*H z)
      (sourceAngularEtaRemainderIntegrand hp hp1 m s ψ z) z := by
    rw [sourceAngularEtaRemainderIntegrand_eq_gapNumerator hp hp1 m s ψ z]
    apply hasDerivAt_root_mul_of_quadratic_equation Q H τ d _ z
      (sourceStandardRoot_analyticAt hp hp1 ψ m z hz.2)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z hz.2) _ (hH z hz.1) (heq z hz.1)
    filter_upwards [(isOpen_ball.sdiff (isClosed_sourcePeriodicSegment hp hp1 ψ m)).mem_nhds hz] with v hv
    exact hQsq v hv
  have hEd (z : ℂ) (hz : z ∈ Λ) : HasDerivAt (fun z => B z*H z)
      (sourceAngularEtaRemainderSheetIntegrand hp hp1 m s ψ w z) z := by
    have hsq : (fun v => B v^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d := by
      filter_upwards [isOpen_ball.mem_nhds hz.1] with v hv
      exact hBsq v hv
    have hd := hasDerivAt_root_mul_of_quadratic_equation B H τ d _ z
      (hB z hz) (hBne z hz) hsq (hH z hz.1) (heq z hz.1)
    rw [sourceAngularEtaRemainderSheetIntegrand_eq_gapNumerator hp hp1 m s ψ w z (hother z hz.1)]
    exact hd
  have hlim (q : ℂ → ℂ) (Y : Set ℂ)
      (hsq : ∀ z ∈ Y, q z^2 = quadraticRootPolynomial τ d z)
      (a : ℂ) (ha : a ∈ Ω) (hzero : quadraticRootPolynomial τ d a = 0) :
      Tendsto (fun z => q z*H z) (𝓝[Y] a) (𝓝 0) := by
    have hpoly := (hasDerivAt_quadraticRootPolynomial τ d a).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Y))
    rw [hzero] at hpoly
    have hsqLim : Tendsto (fun z => q z^2) (𝓝[Y] a) (𝓝 0) :=
      hpoly.congr' (Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => (hsq z hz).symm))
    simpa only [zero_mul] using (tendsto_zero_of_sq_tendsto_zero q hsqLim).mul
      ((hH a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let u := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  have hl : l ∈ Ω := D.gap_enclosed ψ hψ (left_mem_segment ℝ _ _)
  have hu : u ∈ Ω := D.gap_enclosed ψ hψ (right_mem_segment ℝ _ _)
  have hlzero : quadraticRootPolynomial τ d l = 0 := by
    rw [show quadraticRootPolynomial τ d l = sourceAngularSelectedPolynomial hp hp1 ψ m l from rfl,
      sourceAngularSelectedPolynomial_eq_endpoint_factor]
    simp [l]
  have huzero : quadraticRootPolynomial τ d u = 0 := by
    rw [show quadraticRootPolynomial τ d u = sourceAngularSelectedPolynomial hp hp1 ψ m u from rfl,
      sourceAngularSelectedPolynomial_eq_endpoint_factor]
    simp [u]
  refine ⟨hFd,hlim Q X hQsq l hl hlzero,hlim Q X hQsq u hu huzero,?_,hEd,
    hlim B Λ (fun z hz => hBsq z hz.1) l hl hlzero,
    hlim B Λ (fun z hz => hBsq z hz.1) u hu huzero,?_⟩
  · intro z hz
    exact (hB z hz).mul (hH z hz.1)
  · intro z hz
    have hQz := hQsq z ⟨hz.1.1,hz.2⟩
    have hSsq : S z^2 = K z^2*Q z^2 := by
      have h := (hBsq z hz.1.1).trans hQz.symm
      change (S z/K z)^2 = Q z^2 at h
      rw [div_pow] at h
      have he := (div_eq_iff (pow_ne_zero 2 (hKne z hz.1.1))).mp h
      linear_combination he
    have hfull : sourceCanonicalRoot hp hp1 ψ z = K z*Q z := by
      rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
      dsimp only [K,Q]
      ring
    change B z*H z = (sourceCanonicalRoot hp hp1 ψ z/S z)*(Q z*H z-0)
    rw [hfull,sub_zero]
    dsimp only [B]
    have hSz : S z ≠ 0 := sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.1.2
    have hKz : K z ≠ 0 := hKne z hz.1.1
    field_simp [hKz,hSz]
    linear_combination H z*hSsq

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
