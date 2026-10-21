import NLS.Fourier.LineGalileanFourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Complex.RealDeriv

/-! # Angular modulation and translation of Schwartz tests

This implements the Galilean statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped SchwartzMap FourierTransform ContDiff
namespace NLS.Fourier

/-- An arbitrary real angular phase on the line. -/
def lineAngularPhase (ν θ x : ℝ) : ℂ := Complex.exp ((ν*x+θ:ℝ)*Complex.I)

@[fun_prop] theorem contDiff_lineAngularPhase (ν θ : ℝ) :
    ContDiff ℝ ∞ (lineAngularPhase ν θ) := by
  have hr : ContDiff ℝ ∞ (fun x : ℝ => ν*x+θ) := by fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const).cexp

theorem deriv_lineAngularPhase (ν θ : ℝ) :
    deriv (lineAngularPhase ν θ) = fun x => ((ν:ℂ)*Complex.I)*lineAngularPhase ν θ x := by
  funext x
  have h := ((((hasDerivAt_id x).const_mul ν).add_const θ).ofReal_comp.mul_const Complex.I).cexp
  have he := h.deriv
  change deriv (lineAngularPhase ν θ) x = _ at he
  rw [he]
  simp only [id_eq,mul_one]
  unfold lineAngularPhase
  ring

theorem iteratedDeriv_lineAngularPhase (ν θ : ℝ) (k : ℕ) :
    iteratedDeriv k (lineAngularPhase ν θ) =
      fun x => ((ν:ℂ)*Complex.I)^k*lineAngularPhase ν θ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ',deriv_lineAngularPhase]
    funext x
    rw [iteratedDeriv_const_mul_field,ih]
    simp [pow_succ,mul_assoc,mul_comm]

/-- Real angular phases are genuine smooth multipliers of Schwartz space. -/
theorem lineAngularPhase_hasTemperateGrowth (ν θ : ℝ) :
    (lineAngularPhase ν θ).HasTemperateGrowth := by
  refine ⟨contDiff_lineAngularPhase ν θ, fun k => ⟨0, ‖(ν:ℂ)*Complex.I‖^k,?_⟩⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_lineAngularPhase]
  have hn : ‖lineAngularPhase ν θ x‖ = 1 := norm_exp_ofReal_mul_I (ν*x+θ)
  simp [norm_pow,hn]

/-- Actual modulation and translation as a continuous linear map on Schwartz tests. -/
def lineSchwartzModulationTranslation (ν a θ : ℝ) : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (lineAngularPhase ν θ)).comp
    (SchwartzMap.compSubConstCLM ℂ a)

@[simp] theorem lineSchwartzModulationTranslation_apply (ν a θ : ℝ)
    (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    lineSchwartzModulationTranslation ν a θ g x = lineModulationTranslation ν a θ g x := by
  rw [lineSchwartzModulationTranslation,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply (lineAngularPhase_hasTemperateGrowth ν θ),
    SchwartzMap.compSubConstCLM_apply,smul_eq_mul]
  rfl

/-- The actual Schwartz Fourier transform has the same exact full-line formula. -/
theorem fourier_lineSchwartzModulationTranslation (ν a θ : ℝ)
    (g : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 (lineSchwartzModulationTranslation ν a θ g) ξ =
      Complex.exp ((ν*a+θ-2*Real.pi*a*ξ:ℝ)*Complex.I)*𝓕 g (ξ-ν/(2*Real.pi)) := by
  have he : (lineSchwartzModulationTranslation ν a θ g : ℝ → ℂ) =
      lineModulationTranslation ν a θ g := funext (lineSchwartzModulationTranslation_apply ν a θ g)
  change 𝓕 (lineSchwartzModulationTranslation ν a θ g : ℝ → ℂ) ξ = _
  rw [he]
  exact fourier_lineModulationTranslation ν a θ g ξ

end NLS.Fourier
