import NLS.ZakharovShabat.SourceRenormalizedImageFlow

/-! # Local existence and an invariant small-data neighborhood

The open Birkhoff image gives a common time interval for nearby initial
sources at every finite exponent above one. A ball in complex Birkhoff
coordinates stays inside that image for all time: phase rotations preserve
its norm, and the bounded real decoder controls the image condition.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Nearby initial sources have a common positive interval of existence. -/
theorem exists_local_renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) :
    ∃ T > 0, ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ τ ∈ Icc (-T) T, (τ,ψ) ∈ A.renormalizedImageDomain t := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp
    (A.isOpen_renormalizedImageDomain hs hP hr D) (0,φ) (A.zero_mem_renormalizedImageDomain D φ)
  refine ⟨ε/2,by positivity,Metric.ball φ (ε/2),Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity),?_⟩
  intro ψ hψ τ hτ
  apply hball
  rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  refine ⟨?_,lt_trans hψ (by linarith)⟩
  rw [Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt (abs_le.mpr hτ) (by linarith)

/-- Negative time is admissible after any admissible forward step. -/
theorem neg_mem_renormalizedImageDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ A.renormalizedImageDomain t) :
    (-τ,A.renormalizedImageFlow D φ τ) ∈ A.renormalizedImageDomain t := by
  rw [A.mem_imageDomain_restart_iff hs D φ (-τ) τ h,neg_add_cancel]
  exact A.zero_mem_renormalizedImageDomain D φ

/-- Every admissible flow step is reversed by negative time. -/
theorem renormalizedImageFlow_neg (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ A.renormalizedImageDomain t) :
    A.renormalizedImageFlow D (A.renormalizedImageFlow D φ τ) (-τ) = φ := by
  rw [A.renormalizedImageFlow_add hs D φ (-τ) τ h,neg_add_cancel,A.renormalizedImageFlow_zero]

/-- A small ball of complex Birkhoff coordinates stays in the actual real image for all time. -/
theorem exists_small_renormalizedImageDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ ε > 0, ∀ φ : realTypeSourceSubmodule p,
      ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ < ε →
      ∀ τ : ℝ, (τ,φ) ∈ A.renormalizedImageDomain t := by
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
    ‖Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ τ)‖ ≤
        C * ‖A.renormalizedPhaseTrajectory t φ τ‖ :=
      (Birkhoff.decodeReal (p := p)).le_opNorm (A.renormalizedPhaseTrajectory t φ τ)
    _ = C * ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ := by
      rw [renormalizedPhaseTrajectory,Birkhoff.norm_phaseFlow]
    _ ≤ (C+1) * ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ := by
      nlinarith [norm_nonneg (sourceComplexBirkhoffMap hp hp1 t φ.val)]
    _ < δ := by
      have hc : 0 < C+1 := by positivity
      simpa only [mul_comm] using (lt_div_iff₀ hc).mp hφ

/-- There is an open invariant source neighborhood of zero on which the flow is global. -/
theorem exists_invariant_small_renormalizedFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ (0 : realTypeSourceSubmodule p) ∈ V ∧
      (∃ r > 0, Metric.ball 0 r ⊆ V) ∧
      (∀ φ ∈ V, ∀ τ : ℝ, (τ,φ) ∈ A.renormalizedImageDomain t) ∧
      ∀ φ ∈ V, ∀ τ : ℝ, A.renormalizedImageFlow D φ τ ∈ V := by
  obtain ⟨ε,hε,hsmall⟩ := A.exists_small_renormalizedImageDomain D
  let V : Set (realTypeSourceSubmodule p) :=
    {φ | ‖sourceComplexBirkhoffMap hp hp1 t φ.val‖ < ε}
  have hopen : IsOpen V := isOpen_lt D.continuous_complex_map_real.norm continuous_const
  have hz : (0 : realTypeSourceSubmodule p) ∈ V := by
    change ‖sourceComplexBirkhoffMap hp hp1 t 0‖ < ε
    simpa only [D.complex_map_zero,norm_zero] using hε
  refine ⟨V,hopen,hz,Metric.isOpen_iff.mp hopen 0 hz,fun φ hφ τ => hsmall φ hφ τ,?_⟩
  intro φ hφ τ
  change ‖sourceComplexBirkhoffMap hp hp1 t (A.renormalizedImageFlow D φ τ).val‖ < ε
  rw [A.complex_map_renormalizedImageFlow D φ τ (hsmall φ hφ τ),
    renormalizedPhaseTrajectory,Birkhoff.norm_phaseFlow]
  exact hφ

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
