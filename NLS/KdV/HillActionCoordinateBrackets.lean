import NLS.KdV.HillWeakHamiltonianUniqueness
import NLS.KdV.HillAbelianCoordinateVariation

/-! # Physical action-coordinate Hamiltonian pairings

The direction is characterized by the actual Gardner weak identity and
proved unique. The mixed identities therefore concern the physical actions,
not an abstract action model. The local angle orientation agrees with the
physical phase exp(-i theta); full angle-angle canonicality remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Physical actions commute along every physical action Hamiltonian vector. -/
theorem fderiv_hillRealAction_action_hamiltonian_eq_zero
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (A B : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hB : DifferentiableAt ℂ B (SpectralWeight.one.toCoeff q))
    (hAmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (hBmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ))
    (v : Coeff 2) (hv : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) B v) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff q)) v=0 := by
  have hy := hillL2TracePeriodDirection_is_action_hamiltonian q hq hr m hm B hB hBmatch
  rw [hv.unique hy,fderiv_hillRealGapAction_extension_apply q hq hr n hn A hA hAmatch _
    (hillL2TracePeriodDirection_mem_parity q hq hr m hm)]
  simp only [fderiv_hillL2Discriminant_tracePeriodDirection q hq hr m hm,zero_div]
  simp [circleIntegral]

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The mixed coordinate/action Gardner identity at every real source,
including arbitrary closed gaps, for every matching coordinate extension. -/
theorem fderiv_hillAbelianCoordinate_action_hamiltonian
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (C B : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hB : DifferentiableAt ℂ B (SpectralWeight.one.toCoeff q))
    (hCmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (hBmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ))
    (v : Coeff 2) (hv : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) B v) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) v=
      I*(if m=n then 1 else 0)*hillDirichletAbelianCoordinate q hq hr n hn := by
  have hy := hillL2TracePeriodDirection_is_action_hamiltonian q hq hr m hm B hB hBmatch
  rw [hv.unique hy]
  exact fderiv_hillDirichletAbelianCoordinate_extension_tracePeriodDirection q hq hr h0q h0r n m hn hm C hC hCmatch

/-- A genuine local physical angle with the action-conjugate orientation.
Its phase is exp(-i theta), and its derivative along the physical m-th
action Hamiltonian vector is -delta_mn. No angle-angle bracket is assumed. -/
theorem exists_hillActionOrientedAbelianAngle
    (n : ℕ) (hn : 1≤n) (ho : hillRealGapHalfLength q hq hr n≠0) :
    ∃ θ : Coeff 2 → ℂ, AnalyticAt ℂ θ (SpectralWeight.one.toCoeff q) ∧
      (∀ m : ℕ, ∀ _ : 1≤m, (fderiv ℂ θ (SpectralWeight.one.toCoeff q))
        (hillL2TracePeriodDirection q hq hr m)=-(if m=n then 1 else 0)) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (θ (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        exp (-I*θ (SpectralWeight.one.toCoeff p.val))=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn := by
  obtain ⟨A,ε,e,hA,_hε,_hε0,_he,hDA,hphysical⟩ :=
    exists_hillDirichletAbelianAngle_gardner_variation q hq hr h0q h0r n hn ho
  let θ : Coeff 2 → ℂ := fun p => -A p
  have hθ : AnalyticAt ℂ θ (SpectralWeight.one.toCoeff q) := hA.neg
  refine ⟨θ,hθ,?_,?_⟩
  · intro m hm
    have hd := hA.differentiableAt.hasFDerivAt.neg.fderiv
    change fderiv ℂ θ (SpectralWeight.one.toCoeff q)=_ at hd
    rw [hd]
    change -((fderiv ℂ A (SpectralWeight.one.toCoeff q)) (hillL2TracePeriodDirection q hq hr m))=_
    rw [fderiv_hillAbelianAngle_tracePeriodDirection q hq hr n m hn hm A hDA]
  · filter_upwards [hphysical] with p hp
    refine ⟨hp.1,?_,?_⟩
    · change (-A (SpectralWeight.one.toCoeff p.val)).im=0
      rw [neg_im,hp.2.2.2.2.2,neg_zero]
    · change exp (-I*(-A (SpectralWeight.one.toCoeff p.val)))=_
      rw [neg_mul_neg,hp.2.2.2.2.1]
      exact (hillDirichletAbelianPhase_eq_exp_terminal p.val p.property.1 p.property.2 n hn hp.1 _
        hp.2.2.1 hp.2.2.2.1).symm

end NLS.KdV
