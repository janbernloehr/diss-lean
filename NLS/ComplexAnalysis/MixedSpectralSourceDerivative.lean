import NLS.ComplexAnalysis.JointSpectralDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commuting spectral and source derivatives

The analytic joint Fréchet derivative gives both coordinate
derivatives. Symmetry of the second Fréchet derivative then permits
their interchange.
-/

noncomputable section
open Set
open scoped Topology
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The source derivative of a jointly differentiable family is its
joint Fréchet derivative in the source coordinate. -/
theorem fderiv_source_section_eq_joint
    (F : ℂ × A → ℂ) (z : ℂ) (a : A)
    (hF : DifferentiableAt ℂ F (z,a)) :
    fderiv ℂ (fun b : A => F (z,b)) a =
      (fderiv ℂ F (z,a)).comp (ContinuousLinearMap.inr ℂ ℂ A) := by
  have hinr : HasFDerivAt (fun b : A => (z,b))
      (ContinuousLinearMap.inr ℂ ℂ A) a := by
    have hmap : (ContinuousLinearMap.inr ℂ ℂ A) =
        (0 : A →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ A) := by
      ext v <;> simp
    rw [hmap]
    simpa using (hasFDerivAt_const z a).prodMk (hasFDerivAt_id a)
  simpa only [Function.comp_def] using (hF.hasFDerivAt.comp a hinr).fderiv

/-- Source differentiation of the spectral component of the joint
Fréchet derivative agrees with spectral differentiation of its source
component. -/
theorem fderiv_source_spectral_fderiv_eq_deriv_spectral_source_fderiv
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (_hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (z : ℂ) (a : A) (hza : (z,a) ∈ D) (h : A) :
    (fderiv ℂ (fun b : A => (fderiv ℂ F (z,b)) (1,0)) a) h =
      deriv (fun w : ℂ => (fderiv ℂ F (w,a)) (0,h)) z := by
  have hF' : DifferentiableAt ℂ (fderiv ℂ F) (z,a) :=
    ((hF.fderiv) (z,a) hza).differentiableAt
  have hinr : HasFDerivAt (fun b : A => (z,b))
      (ContinuousLinearMap.inr ℂ ℂ A) a := by
    have hmap : (ContinuousLinearMap.inr ℂ ℂ A) =
        (0 : A →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ A) := by
      ext v <;> simp
    rw [hmap]
    simpa using (hasFDerivAt_const z a).prodMk (hasFDerivAt_id a)
  have hinl : HasDerivAt (fun w : ℂ => (w,a)) (1,0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z a)
  have heval₁ : HasFDerivAt
      (fun x : ℂ × A => (fderiv ℂ F x) (1,0))
      ((fderiv ℂ (fderiv ℂ F) (z,a)).flip (1,0)) (z,a) := by
    simpa using hF'.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1,0) : ℂ × A) (z,a))
  have heval₂ : HasFDerivAt
      (fun x : ℂ × A => (fderiv ℂ F x) (0,h))
      ((fderiv ℂ (fderiv ℂ F) (z,a)).flip (0,h)) (z,a) := by
    simpa using hF'.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0,h) : ℂ × A) (z,a))
  have hl := (heval₁.comp a hinr).fderiv
  have hr := (heval₂.comp_hasDerivAt z hinl).deriv
  have hs : IsSymmSndFDerivAt ℂ F (z,a) :=
    ((hF (z,a) hza).contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  change (fderiv ℂ ((fun x : ℂ × A => (fderiv ℂ F x) (1,0)) ∘
      Prod.mk z) a) h =
    deriv ((fun x : ℂ × A => (fderiv ℂ F x) (0,h)) ∘
      fun w : ℂ => (w,a)) z
  rw [hl, hr]
  simpa using (hs.eq (0,h) (1,0))

/-- For a jointly analytic family, source differentiation of its
spectral derivative equals spectral differentiation of its source
Fréchet derivative in every source direction. -/
theorem fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (z : ℂ) (a : A) (hza : (z,a) ∈ D) (h : A) :
    (fderiv ℂ (fun b : A => deriv (fun w : ℂ => F (w,b)) z) a) h =
      deriv (fun w : ℂ =>
        (fderiv ℂ (fun b : A => F (w,b)) a) h) z := by
  have hsourceOpen : IsOpen {b : A | (z,b) ∈ D} :=
    hD.preimage (continuous_const.prodMk continuous_id)
  have hsourceEventually :
      (fun b : A => deriv (fun w : ℂ => F (w,b)) z) =ᶠ[𝓝 a]
        (fun b : A => (fderiv ℂ F (z,b)) (1,0)) := by
    filter_upwards [hsourceOpen.mem_nhds hza] with b hb
    exact deriv_spectral_section_eq_fderiv F z b
      ((hF (z,b) hb).differentiableAt)
  have hspectralOpen : IsOpen {w : ℂ | (w,a) ∈ D} :=
    hD.preimage (continuous_id.prodMk continuous_const)
  have hspectralEventually :
      (fun w : ℂ => (fderiv ℂ (fun b : A => F (w,b)) a) h) =ᶠ[𝓝 z]
        (fun w : ℂ => (fderiv ℂ F (w,a)) (0,h)) := by
    filter_upwards [hspectralOpen.mem_nhds hza] with w hw
    rw [fderiv_source_section_eq_joint F w a
      ((hF (w,a) hw).differentiableAt)]
    simp
  rw [hsourceEventually.fderiv_eq, hspectralEventually.deriv_eq]
  exact fderiv_source_spectral_fderiv_eq_deriv_spectral_source_fderiv
    F D hD hF z a hza h

end NLS.ComplexAnalysis
