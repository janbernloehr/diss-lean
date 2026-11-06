import NLS.KdV.HillLinearDirichletContourComparison
import NLS.KdV.HillFiniteGapDirichletMoments

/-! # The exact actual finite-gap Dirichlet leading residue -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

/-- The actual normalized Dirichlet quotient has leading residue -2*n*pi.
The normalization follows from actual linear periods and quantitative
Dirichlet comparison; no fixed product prefactor or translation law is assumed. -/
theorem hillFiniteGapDirichletResidueMoment_zero_order_eq
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength (hillContinuousCoefficients Q) hq hr k=0) :
    hillDirichletResidueMoment (hillContinuousCoefficients Q) hq hr n hn N 0=-2*(n:ℂ)*Real.pi := by
  let q := hillContinuousCoefficients Q
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let S₀ := hillDirichletResidueMoment q hq hr n hn N 0
  let f := hillL2OddKernel q 0 P
  let g := fun E => (1/2:ℂ)*(P E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)
  have herror := tendsto_hillFiniteGap_linear_contour_sub_dirichlet Q hq hr hreal hf hp hmean n N hn hclosed
  obtain ⟨R,_hR,hlinear⟩ := exists_hillFiniteGap_linear_period q hq hr n N hn hnN hclosed
  have hlarge : ∀ᶠ M : ℕ in atTop, R<(centralCircleRadius M)^2 := by
    filter_upwards [tendsto_centralCircleRadius_atTop.eventually_gt_atTop (max R 1)] with M hM
    have hMR : R<centralCircleRadius M := (le_max_left _ _).trans_lt hM
    have hM1 : 1<centralCircleRadius M := (le_max_right _ _).trans_lt hM
    nlinarith
  have hdir := eventually_circleIntegral_hillFiniteGapDirichlet_moment q hq hr n N hn hnN hclosed 0
  have heq : (fun M : ℕ => (∮ E in C(0,(centralCircleRadius M)^2), f E)-
      (∮ E in C(0,(centralCircleRadius M)^2), g E)) =ᶠ[atTop]
      (fun _ => -2*I*(n:ℂ)*(Real.pi:ℂ)^2-(Real.pi*I:ℂ)*S₀) := by
    filter_upwards [hlarge,hdir] with M hM hD
    simp only [pow_zero,one_mul] at hD
    dsimp only [f,g,P]
    rw [hlinear _ hM,circleIntegral.integral_const_mul,hD]
    dsimp only [S₀]
    ring
  have hconst : Tendsto (fun _ : ℕ => -2*I*(n:ℂ)*(Real.pi:ℂ)^2-(Real.pi*I:ℂ)*S₀) atTop (𝓝 0) :=
    herror.congr' heq
  have he : -2*I*(n:ℂ)*(Real.pi:ℂ)^2-(Real.pi*I:ℂ)*S₀=0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  have hc : (Real.pi*I:ℂ)≠0 := mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  apply mul_left_cancel₀ hc
  change (Real.pi*I:ℂ)*S₀=(Real.pi*I:ℂ)*(-2*(n:ℂ)*Real.pi)
  linear_combination -he

end NLS.KdV
