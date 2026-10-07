import NLS.SequenceSpaces.SpectralConvolution
import NLS.SequenceSpaces.ConjugateReflection
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # The defocusing cubic NLS nonlinearity in weighted ℓ¹

The coefficient product is actual convolution and physical conjugation reverses
indices. The cubic field has a time-independent Lipschitz bound on each ball.
-/
noncomputable section
open Set Complex
namespace NLS.Fourier

/-- Fourier coefficients of the conjugate physical function. -/
def nlsConjugate (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff w.toWeight 1 := WeightedCoeff.conjugateReflection w.toWeight w.neg_eq a

@[simp] theorem nlsConjugate_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) (n : ℤ) :
    (nlsConjugate w a).val n = (starRingEnd ℂ) (a.val (-n)) :=
  WeightedCoeff.conjugateReflection_apply _ _ _ _

@[simp] theorem norm_nlsConjugate (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    ‖nlsConjugate w a‖ = ‖a‖ := WeightedCoeff.norm_conjugateReflection _ _ _

@[simp] theorem nlsConjugate_sub (w : SpectralWeight) (a b : WeightedCoeff w.toWeight 1) :
    nlsConjugate w (a-b) = nlsConjugate w a - nlsConjugate w b := by
  apply Subtype.ext
  funext n
  simp [WeightedCoeff.sub_val]

/-- Physical conjugation is an isometry on the real Banach space. -/
theorem isometry_nlsConjugate (w : SpectralWeight) : Isometry (nlsConjugate w) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  simp only [dist_eq_norm]
  rw [← nlsConjugate_sub,norm_nlsConjugate]

/-- The cubic part of u_t = i u_xx - 2i |u|² u, in original Fourier coefficients. -/
def cubicNLS (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff w.toWeight 1 :=
  (-2*I : ℂ) • w.convolution (w.convolution a a) (nlsConjugate w a)

theorem continuous_cubicNLS (w : SpectralWeight) : Continuous (cubicNLS w) := by
  have hpair : Continuous (fun a : WeightedCoeff w.toWeight 1 => w.convolution a a) :=
    w.convolutionCLM.continuous.clm_apply continuous_id
  exact ((w.convolutionCLM.continuous.comp hpair).clm_apply
    (isometry_nlsConjugate w).continuous).const_smul (-2*I : ℂ)

/-- The weighted cubic norm is bounded by twice the cube of the input norm. -/
theorem norm_cubicNLS_le (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    ‖cubicNLS w a‖ ≤ 2*‖a‖^3 := by
  have hc : ‖(-2*I : ℂ)‖ = 2 := by norm_num [norm_mul]
  rw [cubicNLS,norm_smul,hc]
  calc
    _ ≤ 2*(‖w.convolution a a‖ * ‖nlsConjugate w a‖) := by gcongr; exact w.norm_convolution_le _ _
    _ ≤ 2*((‖a‖*‖a‖)*‖a‖) := by rw [norm_nlsConjugate]; gcongr; exact w.norm_convolution_le _ _
    _ = _ := by ring

private theorem convolution_sub_left (w : SpectralWeight) (a b c : WeightedCoeff w.toWeight 1) :
    w.convolution (a-b) c = w.convolution a c - w.convolution b c := by
  change (w.convolutionCLM (a-b)) c = _
  rw [map_sub,sub_apply]
  rfl

private theorem convolution_sub_right (w : SpectralWeight) (a b c : WeightedCoeff w.toWeight 1) :
    w.convolution a (b-c) = w.convolution a b - w.convolution a c :=
  map_sub (w.convolutionCLM a) b c

/-- A uniform local Lipschitz estimate for the actual cubic coefficient field. -/
theorem norm_cubicNLS_sub_le (w : SpectralWeight) (R : ℝ)
    (a b : WeightedCoeff w.toWeight 1) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖cubicNLS w a-cubicNLS w b‖ ≤ 6*R^2*‖a-b‖ := by
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have he : w.convolution (w.convolution a a) (nlsConjugate w a) -
      w.convolution (w.convolution b b) (nlsConjugate w b) =
      w.convolution (w.convolution (a-b) a) (nlsConjugate w a) +
      w.convolution (w.convolution b (a-b)) (nlsConjugate w a) +
      w.convolution (w.convolution b b) (nlsConjugate w (a-b)) := by
    rw [nlsConjugate_sub,convolution_sub_left,convolution_sub_right,
      convolution_sub_left,convolution_sub_left,convolution_sub_right]
    abel
  have h₁ : ‖w.convolution (w.convolution (a-b) a) (nlsConjugate w a)‖ ≤ R^2*‖a-b‖ := by
    calc
      _ ≤ ‖w.convolution (a-b) a‖*‖nlsConjugate w a‖ := w.norm_convolution_le _ _
      _ ≤ (‖a-b‖*‖a‖)*‖a‖ := by rw [norm_nlsConjugate]; gcongr; exact w.norm_convolution_le _ _
      _ ≤ (‖a-b‖*R)*R := by gcongr
      _ = _ := by ring
  have h₂ : ‖w.convolution (w.convolution b (a-b)) (nlsConjugate w a)‖ ≤ R^2*‖a-b‖ := by
    calc
      _ ≤ ‖w.convolution b (a-b)‖*‖nlsConjugate w a‖ := w.norm_convolution_le _ _
      _ ≤ (‖b‖*‖a-b‖)*‖a‖ := by rw [norm_nlsConjugate]; gcongr; exact w.norm_convolution_le _ _
      _ ≤ (R*‖a-b‖)*R := by gcongr
      _ = _ := by ring
  have h₃ : ‖w.convolution (w.convolution b b) (nlsConjugate w (a-b))‖ ≤ R^2*‖a-b‖ := by
    calc
      _ ≤ ‖w.convolution b b‖*‖nlsConjugate w (a-b)‖ := w.norm_convolution_le _ _
      _ ≤ (‖b‖*‖b‖)*‖a-b‖ := by rw [norm_nlsConjugate]; gcongr; exact w.norm_convolution_le _ _
      _ ≤ (R*R)*‖a-b‖ := by gcongr
      _ = _ := by ring
  have hc : ‖(-2*I : ℂ)‖ = 2 := by norm_num [norm_mul]
  rw [cubicNLS,cubicNLS,← smul_sub,norm_smul,hc,he]
  calc
    _ ≤ 2*((‖w.convolution (w.convolution (a-b) a) (nlsConjugate w a)‖ +
      ‖w.convolution (w.convolution b (a-b)) (nlsConjugate w a)‖) +
      ‖w.convolution (w.convolution b b) (nlsConjugate w (a-b))‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2*((R^2*‖a-b‖+R^2*‖a-b‖)+R^2*‖a-b‖) := by gcongr
    _ = _ := by ring

end NLS.Fourier
