import NLS.KdV.HillDirichletSpectralTerminalVelocity
import NLS.KdV.HillNativeRealSignedMap
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-! Local integral curves of the actual native indexed fields on the
complete physical real mean-zero source. Picard-Lindelof constructs the
curves; their discriminant conservation follows from the native field. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

def hillRealMeanZeroInclusion : HillRealMeanZeroSource →L[ℝ] PeriodOneHminusOne :=
  ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.restrictScalars ℝ).comp
    (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2).subtypeL

theorem hillRealMeanZeroInclusion_apply (q : HillRealMeanZeroSource) :
    hillRealMeanZeroInclusion q=q.val.val := rfl

def hillRealMeanZeroProjection : PeriodOneHminusOne →L[ℝ] HillRealMeanZeroSource :=
  (WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))).comp
    ((WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1))).restrictScalars ℝ)

theorem hillRealMeanZeroProjection_inclusion (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hz : q.val 0=0) :
    hillRealMeanZeroInclusion (hillRealMeanZeroProjection q)=q := by
  have he := WeightedCoeff.zeroModeProjection_coe (Weight.sobolev (-1)) q hz
  have hreal : WeightedCoeff.zeroModeProjection (Weight.sobolev (-1)) q ∈
      WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2 := by
    intro k
    change (WeightedCoeff.zeroModeProjection (Weight.sobolev (-1)) q).val.val (-k)=
      (starRingEnd ℂ) ((WeightedCoeff.zeroModeProjection (Weight.sobolev (-1)) q).val.val k)
    rw [he]
    exact hr k
  have hp := WeightedCoeff.fourierRealZeroProjection_coe (Weight.sobolev (-1))
    (Weight.sobolev_neg (-1)) (WeightedCoeff.zeroModeProjection (Weight.sobolev (-1)) q) hreal
  change ((WeightedCoeff.fourierRealZeroProjection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))
    (WeightedCoeff.zeroModeProjection (Weight.sobolev (-1)) q) : HillMeanZeroSource) : PeriodOneHminusOne)=q
  rw [hp,he]

def hillRealDirichletSpectralVector (k : ℕ+) (q : HillRealMeanZeroSource) : HillRealMeanZeroSource :=
  hillRealMeanZeroProjection (hillHminusDirichletSpectralVector k (hillRealMeanZeroInclusion q))

theorem hillRealDirichletSpectralVector_inclusion (k : ℕ+) (q : HillRealMeanZeroSource) :
    hillRealMeanZeroInclusion (hillRealDirichletSpectralVector k q)=
      hillHminusDirichletSpectralVector k (hillRealMeanZeroInclusion q) :=
  hillRealMeanZeroProjection_inclusion _
    (hillHminusDirichletSpectralVector_real k _ q.property)
    (hillHminusDirichletSpectralVector_zero_mode k _)

theorem contDiff_hillRealDirichletSpectralVector (k : ℕ+) :
    ContDiff ℝ 1 (hillRealDirichletSpectralVector k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hX : ContDiffAt ℝ 1 (hillHminusDirichletSpectralVector k) (hillRealMeanZeroInclusion q) :=
    (analyticOnNhd_hillHminusDirichletSpectralVector k _
      (real_mem_hillHminusCanonicalDirichletDomain _ q.property)).contDiffAt.restrict_scalars ℝ
  have hP : ContDiffAt ℝ 1 hillRealMeanZeroProjection
      (hillHminusDirichletSpectralVector k (hillRealMeanZeroInclusion q)) :=
    (@ContinuousLinearMap.contDiff ℝ PeriodOneHminusOne HillRealMeanZeroSource
      inferInstance inferInstance inferInstance inferInstance inferInstance 1 hillRealMeanZeroProjection).contDiffAt
  have hI : ContDiffAt ℝ 1 hillRealMeanZeroInclusion q :=
    (@ContinuousLinearMap.contDiff ℝ HillRealMeanZeroSource PeriodOneHminusOne
      inferInstance inferInstance inferInstance inferInstance inferInstance 1 hillRealMeanZeroInclusion).contDiffAt
  exact hP.comp q (hX.comp q hI)

theorem exists_hillRealDirichletSpectral_localFlow (k : ℕ+) (q : HillRealMeanZeroSource) :
    ∃ α : HillRealMeanZeroSource → ℝ → HillRealMeanZeroSource,
      ∀ᶠ xt in 𝓝 q ×ˢ 𝓝 (0:ℝ), α xt.1 0=xt.1 ∧
        HasDerivAt (α xt.1) (hillRealDirichletSpectralVector k (α xt.1 xt.2)) xt.2 :=
  (contDiff_hillRealDirichletSpectralVector k).contDiffAt.exists_eventually_eq_hasDerivAt 0

theorem hillHminusDiscriminant_eq_on_spectral_integralCurve (k : ℕ+)
    (γ : ℝ → PeriodOneHminusOne) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (E : ℂ) :
    hillHminusDiscriminant (γ u) E=hillHminusDiscriminant (γ v) E := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => hillHminusDiscriminant (γ τ) E) 0 t := by
    have hc := ((analyticOnNhd_hillHminusDiscriminant_source E (γ t) (mem_univ _)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => hillHminusDiscriminant (γ τ) E)
      (hillHminusDiscriminantCotangent E (γ t) (hillHminusDirichletSpectralVector k (γ t))) t at hc
    rw [hillHminusDirichletSpectralVector_isospectral] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

theorem exists_hillHminusDirichletSpectral_isospectral_integralCurve
    (k : ℕ+) (q : HillRealMeanZeroSource) :
    ∃ γ : ℝ → PeriodOneHminusOne, γ 0=hillRealMeanZeroInclusion q ∧
      (∀ t : ℝ, IsRealPeriodOneHminusOne (γ t) ∧ (γ t).val 0=0) ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t) ∧
        ∀ t ∈ Ioo (-ε) ε, ∀ E : ℂ,
          hillHminusDiscriminant (γ t) E=hillHminusDiscriminant (hillRealMeanZeroInclusion q) E := by
  obtain ⟨α,hα,ε,hε,hder⟩ :=
    (contDiff_hillRealDirichletSpectralVector k).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := q) 0
  let γ : ℝ → PeriodOneHminusOne := fun t => hillRealMeanZeroInclusion (α t)
  have hγ₀ : γ 0=hillRealMeanZeroInclusion q := by change hillRealMeanZeroInclusion (α 0)=_; rw [hα]
  have hγ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t := by
    have hi := @ContinuousLinearMap.hasFDerivAt ℝ inferInstance
      HillRealMeanZeroSource (inferInstance : NormedAddCommGroup HillRealMeanZeroSource).toAddCommGroup
      (inferInstance : NormedSpace ℝ HillRealMeanZeroSource).toModule inferInstance
      PeriodOneHminusOne (inferInstance : NormedAddCommGroup PeriodOneHminusOne).toAddCommGroup
      (inferInstance : NormedSpace ℝ PeriodOneHminusOne).toModule inferInstance
      hillRealMeanZeroInclusion (α t)
    have hc : HasDerivAt (fun τ => hillRealMeanZeroInclusion (α τ))
        (hillRealMeanZeroInclusion (hillRealDirichletSpectralVector k (α t))) t := by
      exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := HillRealMeanZeroSource) (E := PeriodOneHminusOne) t hi
        (hder t (by simpa only [zero_sub,zero_add] using ht))
    change HasDerivAt γ (hillRealMeanZeroInclusion (hillRealDirichletSpectralVector k (α t))) t at hc
    rw [hillRealDirichletSpectralVector_inclusion] at hc
    exact hc
  refine ⟨γ,hγ₀,fun t => ⟨(α t).property,(α t).val.property⟩,ε,hε,hγ,?_⟩
  intro t ht E
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  simpa only [hγ₀] using hillHminusDiscriminant_eq_on_spectral_integralCurve k γ (-ε) ε hγ t 0 ht h0 E

end NLS.KdV
