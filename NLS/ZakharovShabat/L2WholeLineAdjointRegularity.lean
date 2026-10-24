import NLS.ZakharovShabat.L2WholeLineWeakCoordinates
import NLS.FunctionalAnalysis.WeakDerivativeAbsoluteContinuity

/-! # Absolutely continuous representatives of actual whole-line adjoint vectors -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
open scoped ContDiff
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem WholeLineWeakEquation.vector_weak_derivative
    {u : IntervalPairL2} {f g : WholeLineL2}
    (hu : IsClassicalRealType (intervalL2Representative u)) (hfg : WholeLineWeakEquation u f g)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ t : ℝ, deriv ψ t • wholeLineL2Pair f t + ψ t • wholeLineWeakDerivative u f g t) = 0 := by
  have hψC : ContDiff ℝ ∞ (fun t => (ψ t : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hcC : HasCompactSupport (fun t => (ψ t : ℂ)) := hc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hd : deriv (fun t => (ψ t : ℂ)) = fun t => ((deriv ψ t : ℝ) : ℂ) :=
    funext (fun t => ((hψ.differentiable (by norm_num) t).hasDerivAt.ofReal_comp).deriv)
  have h1 := hfg.first_weak_derivative hu (fun t => (ψ t : ℂ)) hψC hcC
  have h2 := hfg.second_weak_derivative hu (fun t => (ψ t : ℂ)) hψC hcC
  rw [hd] at h1 h2
  have hi := ((memLp_wholeLineL2Pair f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    (hψ.continuous_deriv (by norm_num)) hc.deriv
  have hj := (locallyIntegrable_wholeLineWeakDerivative u f g).integrable_smul_left_of_hasCompactSupport
    hψ.continuous hc
  have hk := hi.add hj
  apply Prod.ext
  · change (ContinuousLinearMap.fst ℝ ℂ ℂ) (∫ t : ℝ, deriv ψ t • wholeLineL2Pair f t +
      ψ t • wholeLineWeakDerivative u f g t) = 0
    have hp : (∫ t : ℝ, deriv ψ t • (wholeLineL2Pair f t).1 + ψ t • (wholeLineWeakDerivative u f g t).1) =
        (ContinuousLinearMap.fst ℝ ℂ ℂ) (∫ t : ℝ, deriv ψ t • wholeLineL2Pair f t +
          ψ t • wholeLineWeakDerivative u f g t) := by
      simpa only [Pi.add_apply,ContinuousLinearMap.coe_fst',Prod.fst_add,Prod.smul_fst] using!
        (ContinuousLinearMap.fst ℝ ℂ ℂ).integral_comp_comm hk
    rw [← hp]
    simpa only [Complex.real_smul] using! h1
  · change (ContinuousLinearMap.snd ℝ ℂ ℂ) (∫ t : ℝ, deriv ψ t • wholeLineL2Pair f t +
      ψ t • wholeLineWeakDerivative u f g t) = 0
    have hp : (∫ t : ℝ, deriv ψ t • (wholeLineL2Pair f t).2 + ψ t • (wholeLineWeakDerivative u f g t).2) =
        (ContinuousLinearMap.snd ℝ ℂ ℂ) (∫ t : ℝ, deriv ψ t • wholeLineL2Pair f t +
          ψ t • wholeLineWeakDerivative u f g t) := by
      simpa only [Pi.add_apply,ContinuousLinearMap.coe_snd',Prod.snd_add,Prod.smul_snd] using!
        (ContinuousLinearMap.snd ℝ ℂ ℂ).integral_comp_comm hk
    rw [← hp]
    simpa only [Complex.real_smul] using! h2

/-- An L2 weak solution of the real physical equation has one globally
defined representative that is absolutely continuous on every compact
interval and has the original weak derivative almost everywhere. -/
theorem WholeLineWeakEquation.exists_AC_representative
    {u : IntervalPairL2} {f g : WholeLineL2}
    (hu : IsClassicalRealType (intervalL2Representative u)) (hfg : WholeLineWeakEquation u f g) :
    ∃ F : ℝ → ℂ × ℂ, wholeLineL2Pair f =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      ∀ᵐ t : ℝ, HasDerivAt F (wholeLineWeakDerivative u f g t) t :=
  exists_locally_absolutelyContinuous_of_weak_derivative _ _
    ((memLp_wholeLineL2Pair f).locallyIntegrable (by norm_num))
    (locallyIntegrable_wholeLineWeakDerivative u f g) (hfg.vector_weak_derivative hu)

/-- Every vector in the actual Hilbert adjoint domain has a locally
absolutely continuous representative satisfying the original physical
differential expression with its actual adjoint image. -/
theorem wholeLineMinimalOperator_adjoint_exists_AC_representative
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (f : (wholeLineMinimalOperator u).adjoint.domain) :
    ∃ F : ℝ → ℂ × ℂ, wholeLineL2Pair f =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
        wholeLineL2Pair ((wholeLineMinimalOperator u).adjoint f) := by
  obtain ⟨F,he,hac,hd⟩ := (wholeLineMinimalOperator_adjoint_weakEquation u f).exists_AC_representative hu
  refine ⟨F,he,hac,?_⟩
  filter_upwards [he,hd] with t ht hdt
  simp only [physicalOperator,(HasFDerivAt.hasDerivAt hdt.fst).deriv,
    (HasFDerivAt.hasDerivAt hdt.snd).deriv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,wholeLineWeakDerivative]
  rw [ht]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

end NLS.ZakharovShabat
