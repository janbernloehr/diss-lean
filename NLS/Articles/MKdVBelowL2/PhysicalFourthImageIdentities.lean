import NLS.Articles.MKdVBelowL2.PhysicalFourthImageFlow

/-! # Exact physical coordinates and convergence of the H₄ rotation lift

The prescribed phase curve is recovered under the same Birkhoff map used
in Theorem 1.2. Restarting, inversion, actual actions and uniform source
trajectory convergence are asserted only on their proved open image domains.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical lift has exactly the original coefficients of its actual
source inverse, without an exponent or Fourier normalization change. -/
theorem fourthPhysicalImageFlow_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ : ℝ) :
    physicalRealCoefficientsCL (fourthPhysicalImageFlow hp hp1 u τ) =
      (fourthSourcePhaseFrequency hp hp1).imageFlow (originalBirkhoffChart hp hp1).data.complex
        (physicalRealCoefficientsCL u) τ := physicalRealCoefficientsCL.apply_symm_apply _

/-- The fixed physical Birkhoff map sends the lifted source to precisely
its Hamiltonian rotation with cubic-plus-normalized fourth frequencies. -/
theorem fourthPhysicalImageFlow_coordinates (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthPhysicalImageDomain hp hp1) :
    compatibleBirkhoff hp hp1 (fourthPhysicalImageFlow hp hp1 u τ).val =
      NLS.Birkhoff.hamiltonianPhaseFlow
        ((fourthSourcePhaseFrequency hp hp1).frequency (physicalRealCoefficientsCL u)) τ
        (compatibleBirkhoff hp hp1 u.val) := by
  change sourceComplexBirkhoffMap hp hp1 (originalBirkhoffChart hp hp1).roots
    (physicalRealCoefficientsCL (fourthPhysicalImageFlow hp hp1 u τ)).val = _
  rw [fourthPhysicalImageFlow_coefficients]
  exact (fourthSourcePhaseFrequency hp hp1).complex_map_imageFlow
    (originalBirkhoffChart hp hp1).data.complex (physicalRealCoefficientsCL u) τ h

/-- The actual coordinate products of the fixed physical family are preserved. -/
theorem fourthPhysicalImageFlow_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthPhysicalImageDomain hp hp1) (n : ℤ) :
    (compatibleBirkhoff hp hp1 (fourthPhysicalImageFlow hp hp1 u τ).val).1 n*
      (compatibleBirkhoff hp hp1 (fourthPhysicalImageFlow hp hp1 u τ).val).2 n =
        (compatibleBirkhoff hp hp1 u.val).1 n*(compatibleBirkhoff hp hp1 u.val).2 n := by
  rw [fourthPhysicalImageFlow_coordinates hp hp1 u τ h]
  exact NLS.Birkhoff.phaseFlow_action _ _ _ _

/-- The lifted physical evolution has the original time-addition law. -/
theorem fourthPhysicalImageFlow_add (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ σ : ℝ) (hσ : (σ,u) ∈ fourthPhysicalImageDomain hp hp1) :
    fourthPhysicalImageFlow hp hp1 (fourthPhysicalImageFlow hp hp1 u σ) τ =
      fourthPhysicalImageFlow hp hp1 u (τ+σ) := by
  apply physicalRealCoefficientsCL.injective
  rw [fourthPhysicalImageFlow_coefficients,fourthPhysicalImageFlow_coefficients,
    fourthPhysicalImageFlow_coefficients]
  exact (fourthSourcePhaseFrequency hp hp1).imageFlow_add
    (originalBirkhoffChart hp hp1).data.complex (physicalRealCoefficientsCL u) τ σ hσ

/-- Every admissible physical forward step has an admissible reverse step. -/
theorem neg_mem_fourthPhysicalImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthPhysicalImageDomain hp hp1) :
    (-τ,fourthPhysicalImageFlow hp hp1 u τ) ∈ fourthPhysicalImageDomain hp hp1 := by
  change (-τ,physicalRealCoefficientsCL (fourthPhysicalImageFlow hp hp1 u τ)) ∈
    (fourthSourcePhaseFrequency hp hp1).imageDomain (originalBirkhoffChart hp hp1).data.complex
  rw [fourthPhysicalImageFlow_coefficients]
  exact (fourthSourcePhaseFrequency hp hp1).neg_mem_imageDomain
    (originalBirkhoffChart hp hp1).data.complex (physicalRealCoefficientsCL u) τ h

/-- Negative physical time reverses the admissible step exactly. -/
theorem fourthPhysicalImageFlow_neg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthPhysicalImageDomain hp hp1) :
    fourthPhysicalImageFlow hp hp1 (fourthPhysicalImageFlow hp hp1 u τ) (-τ) = u := by
  rw [fourthPhysicalImageFlow_add hp hp1 u (-τ) τ h,neg_add_cancel,fourthPhysicalImageFlow_zero]

/-- Every sequence or filtered family converging to admissible physical
initial data has uniformly convergent actual source trajectories. No smoothness
or membership assumption on the approximants is needed: openness gives
admissibility eventually on this same compact time interval. -/
theorem tendstoUniformly_fourthPhysicalImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    {ι : Type*} {l : Filter ι} (u : ι → PhysicalRealInput p) (v : PhysicalRealInput p)
    (hv : v ∈ fourthPhysicalTrajectoryDomain hp hp1 T) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun i (τ : Icc (-T) T) => fourthPhysicalImageFlow hp hp1 (u i) τ.val)
      (fun τ => fourthPhysicalImageFlow hp hp1 v τ.val) l := by
  have hcont := (continuousOn_fourthPhysicalTrajectoryOn hp hp1 T v hv).continuousAt
    ((isOpen_fourthPhysicalTrajectoryDomain hp hp1 T).mem_nhds hv)
  have hlim := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hcont.tendsto.comp hu)
  have hbase : (fun τ : Icc (-T) T => fourthPhysicalTrajectoryOn hp hp1 T v τ) =
      fun τ => fourthPhysicalImageFlow hp hp1 v τ.val :=
    funext (fourthPhysicalTrajectoryOn_apply hp hp1 T v hv)
  change TendstoUniformly (fun i (τ : Icc (-T) T) => fourthPhysicalTrajectoryOn hp hp1 T (u i) τ)
    (fun τ => fourthPhysicalTrajectoryOn hp hp1 T v τ) l at hlim
  rw [hbase] at hlim
  have he : (fun i (τ : Icc (-T) T) => fourthPhysicalTrajectoryOn hp hp1 T (u i) τ) =ᶠ[l]
      (fun i τ => fourthPhysicalImageFlow hp hp1 (u i) τ.val) := by
    filter_upwards [hu.eventually ((isOpen_fourthPhysicalTrajectoryDomain hp hp1 T).mem_nhds hv)] with i hi
    exact funext (fourthPhysicalTrajectoryOn_apply hp hp1 T (u i) hi)
  exact (tendstoUniformly_congr he).mp hlim

end NLS.Articles.MKdVBelowL2
