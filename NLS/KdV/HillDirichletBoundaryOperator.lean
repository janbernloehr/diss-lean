import NLS.KdV.HillDirichletGreenBoundary

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- The augmented three-dimensional boundary system. The extra scalar is
the boundary jump, rather than an assumed periodic derivative condition. -/
def hillDirichletBoundaryOperator (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : ((ℂ × ℂ) × ℂ) →L[ℂ] ((ℂ × ℂ) × ℂ) :=
  let F := ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ
  let S := ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ
  (((hillReducedOperator SpectralWeight.one q n hn z hz hcut).comp F)+
    S.smulRight (((1,1) : ℂ × ℂ)+hillModeCoordinates SpectralWeight.one.toWeight 2 n
      (hillBoundaryGreenPotential q n hn n z hz hcut))).prod
    (((hillReconstructionBoundaryRow SpectralWeight.one n (q,z)).comp F)-
      S.smulRight (hillBoundaryGreenTrace q n hn n z hz hcut))

/-- The operator retains the two forced resonant rows and the scalar
Dirichlet boundary row with their original signs and normalization. -/
theorem hillDirichletBoundaryOperator_apply_zero_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) (J : ℂ) :
    hillDirichletBoundaryOperator q n hn z hz hcut (u,J) = 0 ↔
      hillReducedOperator SpectralWeight.one q n hn z hz hcut u =
        -J • (((1,1) : ℂ × ℂ)+hillModeCoordinates SpectralWeight.one.toWeight 2 n
          (hillBoundaryGreenPotential q n hn n z hz hcut)) ∧
      hillReconstructionBoundaryRow SpectralWeight.one n (q,z) u =
        J*hillBoundaryGreenTrace q n hn n z hz hcut := by
  change (((_ : ℂ × ℂ)+J • _,(_ : ℂ)-J*_) : (ℂ × ℂ) × ℂ) = 0 ↔ _
  constructor
  · intro hh
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    refine ⟨?_,sub_eq_zero.mp h2⟩
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  · rintro ⟨h1,h2⟩
    apply Prod.ext
    · change hillReducedOperator SpectralWeight.one q n hn z hz hcut u+J • _ = 0
      rw [h1,neg_smul,neg_add_cancel]
    · exact sub_eq_zero.mpr h2

/-- This augmented kernel is exactly the forced reconstructed solution with
zero physical boundary value. This does not assert an unproved converse
identification of every kernel element with the normalized Dirichlet IVP. -/
theorem hillDirichletBoundaryOperator_kernel_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) (J : ℂ) :
    hillDirichletBoundaryOperator q n hn z hz hcut (u,J) = 0 ↔
      IsHillBoundaryForcedFourierSolution q z n J (hillBoundaryReconstruct q n hn n z hz hcut u J) ∧
      hillUnitBoundaryTrace (hillBoundaryReconstruct q n hn n z hz hcut u J) = 0 := by
  rw [hillDirichletBoundaryOperator_apply_zero_iff]
  have h1 : IsHillBoundaryForcedFourierSolution q z n J (hillBoundaryReconstruct q n hn n z hz hcut u J) ↔
      hillReducedOperator SpectralWeight.one q n hn z hz hcut u =
        -J • (((1,1) : ℂ × ℂ)+hillModeCoordinates SpectralWeight.one.toWeight 2 n
          (hillBoundaryGreenPotential q n hn n z hz hcut)) := by
    simpa using hillBoundaryReconstruct_isForced_iff q n hn n z hz hcut u J
  have h2 := hillBoundaryReconstruct_trace_zero_iff q n hn n z hz hcut u J
  exact (h1.and h2).symm

/-- The original Dirichlet data give an actual augmented kernel vector. -/
theorem hillDirichletBoundaryOperator_actual_kernel (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (z : ℂ) (hzero : hillL2DirichletCharacteristic q z=0)
    (n : ℕ) (hn : 1 ≤ n) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillDirichletBoundaryOperator (hillUnitWeightLift 2 q) n hn z hz
      (by simpa only [norm_hillUnitWeightLift] using hcut)
      (hillL2DirichletResonantModes q z n,hillL2DirichletBoundaryJump q z n) = 0 :=
  (hillDirichletBoundaryOperator_apply_zero_iff _ n hn z hz _ _ _).mpr
    ⟨hillL2DirichletResonantModes_reduced q hq z hzero n hn hz hcut,
      hillL2DirichletResonantModes_boundary_equation q hq z hzero n hn hz hcut⟩

/-- Every actual complex Dirichlet zero in the checked high strip is a zero
of this genuinely derived augmented determinant. No homogeneous periodic
Schur determinant is substituted for the Dirichlet characteristic. -/
theorem hillDirichletBoundaryOperator_det_zero_of_dirichlet (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (z : ℂ) (hzero : hillL2DirichletCharacteristic q z=0)
    (n : ℕ) (hn : 1 ≤ n) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (hillDirichletBoundaryOperator (hillUnitWeightLift 2 q) n hn z hz
      (by simpa only [norm_hillUnitWeightLift] using hcut)).toLinearMap.det = 0 := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot,Submodule.ne_bot_iff]
  refine ⟨(hillL2DirichletResonantModes q z n,hillL2DirichletBoundaryJump q z n),
    hillDirichletBoundaryOperator_actual_kernel q hq z hzero n hn hz hcut,?_⟩
  intro he
  rcases hillL2DirichletResonantModes_or_jump_ne_zero q hq z hzero n hn hz hcut with hu | hJ
  · exact hu (congrArg Prod.fst he)
  · exact hJ (congrArg Prod.snd he)

end NLS.KdV
