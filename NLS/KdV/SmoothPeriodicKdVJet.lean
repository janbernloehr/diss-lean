import NLS.KdV.ClassicalKdVJet
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.KdV

def smoothKdVJetCurve (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ) : Curve ℂ :=
  ⟨fun x => iteratedDeriv j f x,
    (contDiff_iteratedDeriv f hf j).continuous.comp continuous_subtype_val⟩

theorem extend_smoothKdVJetCurve (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    extend (smoothKdVJetCurve f hf j) x = iteratedDeriv j f x := by
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx,smoothKdVJetCurve,ContinuousMap.coe_mk]

theorem ac_smoothKdVJetCurve (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    AbsolutelyContinuousOnInterval (extend (smoothKdVJetCurve f hf j)) 0 1 := by
  have h : ContDiffOn ℝ 1 (iteratedDeriv j f) (uIcc (0 : ℝ) 1) :=
    ((contDiff_iteratedDeriv f hf j).of_le (by simp)).contDiffOn
  apply (h.congr ?_).absolutelyContinuousOnInterval
  intro x hx
  exact extend_smoothKdVJetCurve f hf j x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)

theorem ae_derivative_smoothKdVJetCurve (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (smoothKdVJetCurve f hf j))
        (extend (smoothKdVJetCurve f hf (j+1)) x) x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with x hx hxne
  have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1,lt_of_le_of_ne hx.2 hxne⟩
  have he : extend (smoothKdVJetCurve f hf j) =ᶠ[𝓝 x] iteratedDeriv j f := by
    filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
    exact extend_smoothKdVJetCurve f hf j y ⟨hy.1.le,hy.2.le⟩
  have hd := ((contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv f hf j)).1 x).hasDerivAt
  rw [← iteratedDeriv_succ] at hd
  rw [extend_smoothKdVJetCurve f hf (j+1) x ⟨hx.1.le,hx.2⟩]
  exact hd.congr_of_eventuallyEq he

/-- Every ordinary smooth one-periodic physical function supplies the
spatial data in the PDE definition, with no spectral assumptions. -/
def PeriodicKdVJet.ofSmooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) : PeriodicKdVJet where
  value := smoothKdVJetCurve f hf 0
  first := smoothKdVJetCurve f hf 1
  second := smoothKdVJetCurve f hf 2
  third := smoothKdVJetCurve f hf 3
  ac_value := ac_smoothKdVJetCurve f hf 0
  ac_first := ac_smoothKdVJetCurve f hf 1
  ac_second := ac_smoothKdVJetCurve f hf 2
  derivatives := by
    filter_upwards [ae_derivative_smoothKdVJetCurve f hf 0,
      ae_derivative_smoothKdVJetCurve f hf 1,ae_derivative_smoothKdVJetCurve f hf 2] with x h0 h1 h2
    exact ⟨h0,h1,h2⟩
  periodic_value := by simpa only [smoothKdVJetCurve,ContinuousMap.coe_mk,zero_add] using periodic_iteratedDeriv f 1 hp 0 0
  periodic_first := by simpa only [smoothKdVJetCurve,ContinuousMap.coe_mk,zero_add] using periodic_iteratedDeriv f 1 hp 1 0
  periodic_second := by simpa only [smoothKdVJetCurve,ContinuousMap.coe_mk,zero_add] using periodic_iteratedDeriv f 1 hp 2 0
  periodic_third := by simpa only [smoothKdVJetCurve,ContinuousMap.coe_mk,zero_add] using periodic_iteratedDeriv f 1 hp 3 0

theorem PeriodicKdVJet.ofSmooth_velocity (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (x : Icc (0 : ℝ) 1) :
    (PeriodicKdVJet.ofSmooth f hf hp).velocity x = 6*f x*deriv f x-iteratedDeriv 3 f x := by
  simp only [PeriodicKdVJet.velocity,PeriodicKdVJet.ofSmooth,smoothKdVJetCurve,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
    ContinuousMap.coe_mk,smul_eq_mul,iteratedDeriv_zero,iteratedDeriv_one]
  ring

end NLS.KdV
