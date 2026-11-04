import NLS.KdV.HillBoundaryGreenDecay
import NLS.KdV.HillDirichletBoundaryOperator
import NLS.KdV.HillRootSeparation
import NLS.KdV.HillBoundaryCoordinates
import NLS.ComplexAnalysis.AugmentedBoundaryBalance

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The scalar denominator obtained by eliminating the two resonant
amplitudes and the actual endpoint source from the augmented system. -/
def hillBoundaryScalarDenominator (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (hz : E ∈ reducedHillStrip n)
    (hc : 8*‖q‖ ≤ (n : ℝ)) : ℂ :=
  hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)*
    (1+(hillBoundaryGreenPotential q n hn n E hz hc).val n)+
  hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)*
    (1+(hillBoundaryGreenPotential q n hn n E hz hc).val (-(n : ℤ)))+
  hillBoundaryGreenTrace q n hn n E hz hc*
    (E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q n hn E hz hc)

/-- The genuine Dirichlet data satisfy the scalar augmented balance. Neither
the unweighted potential nor a periodic eigenfunction is substituted for
its original boundary source. -/
theorem hillDirichlet_boundary_scalar_balance
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (E : ℂ) (hzero : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0)
    (n : ℕ) (hn : 1 ≤ n) (hz : E ∈ reducedHillStrip n) (hc : 8*‖q‖ ≤ (n : ℝ)) :
    (E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q n hn E hz hc)*
      hillBoundaryScalarDenominator q n hn E hz hc =
    hillBoundaryGreenTrace q n hn n E hz hc*
      hillUpperCoupling SpectralWeight.one q n hn E hz hc*
      hillLowerCoupling SpectralWeight.one q n hn E hz hc-
    (hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)*
        hillUpperCoupling SpectralWeight.one q n hn E hz hc*
        (1+(hillBoundaryGreenPotential q n hn n E hz hc).val (-(n : ℤ)))+
      hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)*
        hillLowerCoupling SpectralWeight.one q n hn E hz hc*
        (1+(hillBoundaryGreenPotential q n hn n E hz hc).val n)) := by
  let d := E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q n hn E hz hc
  let bp := hillUpperCoupling SpectralWeight.one q n hn E hz hc
  let bm := hillLowerCoupling SpectralWeight.one q n hn E hz hc
  let ap := 1+(hillBoundaryGreenPotential q n hn n E hz hc).val n
  let am := 1+(hillBoundaryGreenPotential q n hn n E hz hc).val (-(n : ℤ))
  let Bp := hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)
  let Bm := hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)
  let t := hillBoundaryGreenTrace q n hn n E hz hc
  let u := hillL2DirichletResonantModes (SpectralWeight.one.toCoeff q) E n
  let J := hillL2DirichletBoundaryJump (SpectralWeight.one.toCoeff q) E n
  have hc0 : 8*‖SpectralWeight.one.toCoeff q‖ ≤ (n : ℝ) := by
    nlinarith [SpectralWeight.one.norm_toCoeff_le q]
  have hR := hillL2DirichletResonantModes_reduced (SpectralWeight.one.toCoeff q) hq E hzero n hn hz hc0
  simp only [hillUnitWeightLift_toCoeff] at hR
  rw [hillReducedOperator_apply] at hR
  have h1 : d*u.1-bp*u.2+J*ap=0 := by
    have hh := congrArg Prod.fst hR
    change d*u.1-bp*u.2 = -J*ap at hh
    linear_combination hh
  have h2 : -bm*u.1+d*u.2+J*am=0 := by
    have hh := congrArg Prod.snd hR
    change d*u.2-bm*u.1 = -J*am at hh
    linear_combination hh
  have h3 : Bp*u.1+Bm*u.2-J*t=0 := by
    have hh := hillL2DirichletResonantModes_boundary_equation
      (SpectralWeight.one.toCoeff q) hq E hzero n hn hz hc0
    simp only [hillUnitWeightLift_toCoeff] at hh
    rw [hillReconstructionBoundaryRow_apply] at hh
    change u.1*Bp+u.2*Bm=J*t at hh
    linear_combination hh
  have hne : u.1 ≠ 0 ∨ u.2 ≠ 0 ∨ J ≠ 0 := by
    by_contra he
    push Not at he
    have hu : u=0 := Prod.ext he.1 he.2.1
    rcases hillL2DirichletResonantModes_or_jump_ne_zero
      (SpectralWeight.one.toCoeff q) hq E hzero n hn hz hc0 with hu0 | hJ0
    · exact hu0 hu
    · exact hJ0 he.2.2
  exact augmented_boundary_diagonal_balance d bp bm ap am Bp Bm t u.1 u.2 J h1 h2 h3 hne

end NLS.KdV
