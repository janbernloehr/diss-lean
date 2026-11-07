import NLS.KdV.KdVFourierField
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Stability of the independent integrated weak KdV equation under locally
uniform physical L² convergence. The nonlinear limit uses the continuous
L² coefficient pairing and a compact-time bound, not spectral invariants. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

theorem norm_kdvFourierModeField_le (a : Coeff 2) (n : ℤ) (B : ℝ)
    (_hB : 0 ≤ B) (ha : ‖a‖ ≤ B) :
    ‖kdvFourierModeField a n‖ ≤
      ‖2*I*(Real.pi:ℂ)*n‖^3*B+3*‖2*I*(Real.pi:ℂ)*n‖*B^2 := by
  unfold kdvFourierModeField
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_neg,norm_pow,norm_ofNat]
  have he : ‖a n‖ ≤ B := (lp.norm_apply_le_norm (by norm_num) a n).trans ha
  have hq : ‖kdvQuadraticMode a n‖ ≤ B^2 :=
    (norm_kdvQuadraticMode_le a n).trans (pow_le_pow_left₀ (norm_nonneg _) ha 2)
  gcongr

/-- Locally uniform L² limits of weak solutions satisfy the same actual
quadratic Fourier equation. Existence of an approximating family is not
asserted here. -/
theorem isFourierWeakKdVCoefficients_of_locallyUniformLimit
    (a : ℕ → ℝ → Coeff 2) (u : ℝ → Coeff 2)
    (ha : ∀ N, IsFourierWeakKdVCoefficients (a N)) (hu : Continuous u)
    (hlim : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn a u atTop (Icc (-T) T)) :
    IsFourierWeakKdVCoefficients u := by
  refine ⟨hu,?_⟩
  intro n s t
  let T := |s|+|t|
  have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs : s ∈ Icc (-T) T := by
    constructor <;> dsimp [T] <;> linarith [neg_abs_le s,le_abs_self s,abs_nonneg t]
  have ht : t ∈ Icc (-T) T := by
    constructor <;> dsimp [T] <;> linarith [neg_abs_le t,le_abs_self t,abs_nonneg s]
  have hsub : uIcc s t ⊆ Icc (-T) T := uIcc_subset_Icc hs ht
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hu.continuousOn (s := Icc (-T) T))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s hs)
  have hBN := (uniformContinuous_norm.comp_tendstoUniformlyOn (hlim T hT)).eventually_forall_le
    (by linarith : B < B+1) hB
  have hint := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := s) (b := t) (μ := volume)
    (F := fun N r => kdvFourierModeField (a N r) n)
    (f := fun r => kdvFourierModeField (u r) n)
    (fun _ => ‖2*I*(Real.pi:ℂ)*n‖^3*(B+1)+3*‖2*I*(Real.pi:ℂ)*n‖*(B+1)^2)
    (Eventually.of_forall (fun N => ((continuous_kdvFourierModeField n).comp (ha N).1).aestronglyMeasurable))
    (hBN.mono (fun N hN => Eventually.of_forall (fun r hr =>
      norm_kdvFourierModeField_le (a N r) n (B+1) (by linarith)
        (hN r (hsub (uIoc_subset_uIcc hr))))))
    intervalIntegrable_const
    (Eventually.of_forall (fun r hr => (continuous_kdvFourierModeField n).continuousAt.tendsto.comp
      ((hlim T hT).tendsto_at (hsub (uIoc_subset_uIcc hr)))))
  have hl := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.continuousAt.tendsto.comp
    ((hlim T hT).tendsto_at ht)).sub
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.continuousAt.tendsto.comp
      ((hlim T hT).tendsto_at hs))
  have hi : Tendsto (fun N => a N t n-a N s n) atTop
      (𝓝 (∫ r in s..t, kdvFourierModeField (u r) n)) :=
    hint.congr' (Eventually.of_forall (fun N => ((ha N).2 n s t).symm))
  exact tendsto_nhds_unique hl hi

end NLS.KdV
