import NLS.ZakharovShabat.SourceActionPhaseFlow

/-! # Local time intervals and an invariant small neighborhood for action phase flows

The source interval is common to all nearby data. The small neighborhood is
chosen once before time and is invariant for every real time.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Nearby initial sources have a common positive interval of existence. -/
theorem exists_local_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) :
    ∃ T > 0, ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ τ ∈ Icc (-T) T, (τ,ψ) ∈ F.imageDomain D := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp
    (F.isOpen_imageDomain D) (0,φ) (F.zero_mem_imageDomain D φ)
  refine ⟨ε/2,by positivity,Metric.ball φ (ε/2),Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity),?_⟩
  intro ψ hψ τ hτ
  apply hball
  rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  refine ⟨?_,lt_trans hψ (by linarith)⟩
  rw [Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt (abs_le.mpr hτ) (by linarith)

/-- A small ball of complex Birkhoff coordinates stays in the actual real image for all time. -/
theorem exists_small_imageDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ ε > 0, ∀ φ : realTypeSourceSubmodule p,
      ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ < ε →
      ∀ τ : ℝ, (τ,φ) ∈ F.imageDomain D := by
  have hz : (0 : RealCoeff p × RealCoeff p) ∈ range (sourceRealBirkhoffMap hp hp1 t) :=
    ⟨0,D.real_map_zero⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp D.real_image_open 0 hz
  let C : ℝ := ‖Birkhoff.decodeReal (p := p)‖
  have hC : 0 ≤ C := norm_nonneg _
  refine ⟨δ/(C+1),by positivity,?_⟩
  intro φ hφ τ
  apply hball
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖Birkhoff.decodeReal (F.phaseTrajectory D φ τ)‖ ≤
        C * ‖F.phaseTrajectory D φ τ‖ :=
      (Birkhoff.decodeReal (p := p)).le_opNorm (F.phaseTrajectory D φ τ)
    _ = C * ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ := by
      rw [F.phaseTrajectory_norm]
    _ ≤ (C+1) * ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ := by
      nlinarith [norm_nonneg (sourceComplexBirkhoffMap hp hp1 t φ.val)]
    _ < δ := by
      have hc : 0 < C+1 := by positivity
      simpa only [mul_comm] using (lt_div_iff₀ hc).mp hφ

/-- There is an open invariant source neighborhood of zero on which the flow is global. -/
theorem exists_invariant_small_phaseFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ (0 : realTypeSourceSubmodule p) ∈ V ∧
      (∃ r > 0, Metric.ball 0 r ⊆ V) ∧
      (∀ φ ∈ V, ∀ τ : ℝ, (τ,φ) ∈ F.imageDomain D) ∧
      ∀ φ ∈ V, ∀ τ : ℝ, F.imageFlow D φ τ ∈ V := by
  obtain ⟨ε,hε,hsmall⟩ := F.exists_small_imageDomain D
  let V : Set (realTypeSourceSubmodule p) :=
    {φ | ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ < ε}
  have hopen : IsOpen V := isOpen_lt D.continuous_complex_map_real.norm continuous_const
  have hz : (0 : realTypeSourceSubmodule p) ∈ V := by
    change ‖sourceComplexBirkhoffMap hp hp1 t 0‖ < ε
    simpa only [D.complex_map_zero,norm_zero] using hε
  refine ⟨V,hopen,hz,Metric.isOpen_iff.mp hopen 0 hz,fun φ hφ τ => hsmall φ hφ τ,?_⟩
  intro φ hφ τ
  change ‖sourceComplexBirkhoffMap hp hp1 t (F.imageFlow D φ τ).val‖ < ε
  rw [F.complex_map_imageFlow D φ τ (hsmall φ hφ τ),
    F.phaseTrajectory_norm]
  exact hφ

end NLS.ZakharovShabat.SourceActionFrequency
