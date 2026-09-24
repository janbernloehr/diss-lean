import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Uniform derivative bounds near a compact spectral circle

For a jointly analytic function on an open spectral/parameter domain,
the joint Fréchet derivative is uniformly bounded on a fixed compact
spectral circle and a sufficiently small parameter neighborhood.
-/

noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Differentiating a joint function in the parameter direction cannot
increase the norm of its full product derivative. -/
theorem norm_fderiv_parameter_section_le
    (F : ℂ × A → ℂ) (z : ℂ) (a : A)
    (hF : DifferentiableAt ℂ F (z,a)) :
    ‖fderiv ℂ (fun b : A => F (z,b)) a‖ ≤ ‖fderiv ℂ F (z,a)‖ := by
  let ι : A →L[ℂ] ℂ × A := ContinuousLinearMap.inr ℂ ℂ A
  have hinc : HasFDerivAt (fun b : A => (z,b)) ι a := by
    exact hasFDerivAt_prodMk_right z a
  have hcomp := hF.hasFDerivAt.comp a hinc
  change ‖fderiv ℂ (F ∘ Prod.mk z) a‖ ≤ ‖fderiv ℂ F (z,a)‖
  rw [hcomp.fderiv]
  calc
    ‖(fderiv ℂ F (z,a)).comp ι‖ ≤ ‖fderiv ℂ F (z,a)‖ * ‖ι‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ F (z,a)‖ := by
      have hι : ‖ι‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℂ ℂ A
      nlinarith [norm_nonneg (fderiv ℂ F (z,a))]

/-- A compact spectral circle in the domain of a jointly analytic
function has a common open parameter neighborhood on which the joint
Fréchet derivative is uniformly bounded. -/
theorem exists_uniform_joint_fderiv_bound_on_circle
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (a : A)
    (hcircle : ∀ z ∈ sphere c R, (z,a) ∈ D) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ sphere c R, ∀ b ∈ V,
          (z,b) ∈ D ∧ ‖fderiv ℂ F (z,b)‖ ≤ M := by
  let K : Set (ℂ × A) := sphere c R ×ˢ {a}
  have hK : IsCompact K := (isCompact_sphere c R).prod isCompact_singleton
  have hKD : K ⊆ D := by
    rintro ⟨z,b⟩ ⟨hz,hb⟩
    have : b = a := hb
    subst b
    exact hcircle z hz
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hDopen (by norm_num)
  obtain ⟨T, hKT, hTopen, hbounded⟩ :=
    exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      hK hDopen hKD hdf
  have hKTD : K ⊆ T ∩ D := fun x hx => ⟨hKT hx, hKD hx⟩
  obtain ⟨U, V, _, hVopen, hKU, haV, hUV⟩ :=
    generalized_tube_lemma (isCompact_sphere c R) isCompact_singleton
      (hTopen.inter hDopen) hKTD
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  refine ⟨V, hVopen, haV (mem_singleton a), max 0 C,
    le_max_left _ _, ?_⟩
  intro z hz b hb
  have hzbTD : (z,b) ∈ T ∩ D := hUV ⟨hKU hz, hb⟩
  have hzbT : (z,b) ∈ T := hzbTD.1
  have hzbD : (z,b) ∈ D := hzbTD.2
  exact ⟨hzbD, (hC _ ⟨(z,b), hzbT, rfl⟩).trans (le_max_right _ _)⟩

end NLS.ComplexAnalysis
