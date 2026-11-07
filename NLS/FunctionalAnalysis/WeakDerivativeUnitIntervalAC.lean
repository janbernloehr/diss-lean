import NLS.FunctionalAnalysis.WeakDerivativeUnitIntervalConstant
import NLS.FunctionalAnalysis.LocallyIntegrablePrimitive

/-! # Closed-interval AC representatives from genuine weak derivatives

The input is interval integrability and compact interior test identities.
No endpoint matching, periodic extension or AC representative is assumed.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace NLS.FunctionalAnalysis

def HasUnitIntervalWeakDerivative (f g : ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo (0:ℝ) 1 →
    (∫ x in (0:ℝ)..1, deriv ψ x • f x+ψ x • g x)=0

theorem exists_unitInterval_ac_of_weak_derivative
    (f g : ℝ → ℂ) (hf : IntegrableOn f (Ioc (0:ℝ) 1)) (hg : IntegrableOn g (Ioc (0:ℝ) 1))
    (hw : HasUnitIntervalWeakDerivative f g) :
    ∃ F : ℝ → ℂ, Continuous F ∧ AbsolutelyContinuousOnInterval F 0 1 ∧
      f =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] F ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt F (g x) x := by
  let f0 := (Ioc (0:ℝ) 1).indicator f
  let g0 := (Ioc (0:ℝ) 1).indicator g
  have hf0 : Integrable f0 volume := hf.integrable_indicator measurableSet_Ioc
  have hg0 : Integrable g0 volume := hg.integrable_indicator measurableSet_Ioc
  have hfg : f0 =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact indicator_of_mem hx f
  have hgg : g0 =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact indicator_of_mem hx g
  have hw0 (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ Ioo (0:ℝ) 1) :
      (∫ x : ℝ, deriv ψ x • f0 x+ψ x • g0 x)=0 := by
    have he : (fun x => deriv ψ x • f0 x+ψ x • g0 x) =
        (Ioc (0:ℝ) 1).indicator (fun x => deriv ψ x • f x+ψ x • g x) := by
      funext x
      by_cases hx : x ∈ Ioc (0:ℝ) 1 <;> simp [f0,g0,hx]
    rw [he,integral_indicator measurableSet_Ioc]
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hw ψ hψ hc hs
  let G := fun x => ∫ t in (0:ℝ)..x, g0 t
  have hGc : Continuous G := continuous_local_primitive hg0.locallyIntegrable 0
  have hGl : LocallyIntegrable G volume := hGc.locallyIntegrable
  have hGa : AbsolutelyContinuousOnInterval G 0 1 :=
    absolutelyContinuousOnInterval_local_primitive hg0.locallyIntegrable 0 0 1
  have hk : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0:ℝ) 1 → (∫ x : ℝ, deriv ψ x • (f0 x-G x))=0 := by
    intro ψ hψ hc hs
    have hi1 := hf0.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by norm_num)) hc.deriv
    have hi2 := hGl.integrable_smul_left_of_hasCompactSupport
      (hψ.continuous_deriv (by norm_num)) hc.deriv
    have hi3 := hg0.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have h1 := hw0 ψ hψ hc hs
    have h2 := integral_deriv_smul_local_primitive_eq_zero hg0.locallyIntegrable 0 ψ hψ hc
    change (∫ x : ℝ, deriv ψ x • G x+ψ x • g0 x)=0 at h2
    rw [integral_add hi1 hi3] at h1
    rw [integral_add hi2 hi3] at h2
    simp only [smul_sub]
    rw [integral_sub hi1 hi2,sub_eq_zero]
    exact add_right_cancel (h1.trans h2.symm)
  obtain ⟨c,hc⟩ := ae_eq_const_on_unitInterval_of_weak_derivative_zero
    (fun x => f0 x-G x) (hf0.locallyIntegrable.sub hGl) hk
  refine ⟨fun x => c+G x,continuous_const.add hGc,absolutelyContinuousOnInterval_const_add hGa c,?_,?_⟩
  · filter_upwards [hc,hfg] with x hx hfx
    rw [hfx] at hx
    exact sub_eq_iff_eq_add.mp hx
  · filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral hg0.locallyIntegrable),hgg]
      with x hx hgx
    simpa only [hgx] using (hx 0).const_add c

end NLS.FunctionalAnalysis
