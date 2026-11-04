import NLS.KdV.HillCubicKernelExterior
import NLS.Articles.KdVKdV2Frequencies.FiniteGapCubicVelocityLimit

/-! # Exact cubic contours of the actual finite-gap KdV velocity

The actual cubic spectral kernel is analytically filled before Cauchy's
theorem is used. The physical velocity is identified by the independently
proved contour limit. No finite-gap-only Hamiltonian value identity is
differentiated as an open source germ.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

/-- At any actual finite-gap source, every sufficiently large cubic
contour equals the physical KdV Dirichlet velocity coefficient. -/
theorem exists_kdvDirichletVelocity_cubic_contour_identity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    ∃ R : ℝ, 0<R ∧ ∀ r : ℝ, R<r →
      CircleIntegrable (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3*
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
          hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E) 0 r ∧
      kdvDirichletVelocitySum Q q n hn N=(4/(I*Real.pi) : ℂ)*
        (∮ E in C(0,r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3*
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let P := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let f := hillL2CubicKernel q.val P
  let a : ℂ := 4/(I*Real.pi)
  have hfg : HillFiniteGap q.val q.property.1 q.property.2 := by
    apply (hillFiniteGap_iff_collapsed_tail q.val q.property.1 q.property.2).2
    refine ⟨N+1,?_⟩
    intro k hk hk1
    have he := hclosed k hk1 (by omega)
    dsimp only [hillRealGapHalfLength] at he
    linarith
  obtain ⟨R,hR,_ha,hperiod⟩ := HillFiniteGap.exists_cubic_exterior_and_periods q.val q.property.1 q.property.2 hfg n hn
  refine ⟨R,hR,?_⟩
  intro r hr
  refine ⟨(hperiod r hr).1,?_⟩
  have hlarge : ∀ᶠ M : ℕ in atTop, R<(centralCircleRadius M)^2 := by
    filter_upwards [tendsto_centralCircleRadius_atTop.eventually_gt_atTop (max R 1)] with M hM
    have hMR : R<centralCircleRadius M := (le_max_left _ _).trans_lt hM
    have hM1 : 1<centralCircleRadius M := (le_max_right _ _).trans_lt hM
    nlinarith
  have heq : (fun M : ℕ => a*(∮ E in C(0,(centralCircleRadius M)^2), f E)) =ᶠ[atTop]
      (fun _ => a*(∮ E in C(0,r), f E)) := by
    filter_upwards [hlarge] with M hM
    exact congrArg (fun z : ℂ => a*z) ((hperiod _ hM).2 r hr)
  have hlim := tendsto_kdv_cubic_frequency_contour Q hreal hf hp hmean n hn N hnN hclosed
  have hconst := hlim.congr' heq
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-- The literal physical KdV scalar coordinate derivative has the exact
cubic spectral contour coefficient at every sufficiently large radius.
Closed selected gaps are included. The radius precedes the choice of
any differentiable nearby-real matching coordinate germ. -/
theorem exists_fderiv_hillDirichletAbelianCoordinate_kdv_cubic_contour
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    ∃ R : ℝ, 0<R ∧ ∀ r : ℝ, R<r →
      ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
        (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        ((4/(I*Real.pi) : ℂ)*(∮ E in C(0,r),
          hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3*
            hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
              hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E))*
                (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  obtain ⟨R,hR,hid⟩ := exists_kdvDirichletVelocity_cubic_contour_identity Q hreal hf hp hmean n hn N hnN hclosed
  refine ⟨R,hR,?_⟩
  intro r hr C hC hmatch
  have hjet := (fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde Q hf hp hreal n hn
    N hclosed C hC hmatch).1
  change (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (kdvFourierDirection _ hf)=
    kdvDirichletVelocitySum Q q n hn N*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) at hjet
  rw [(hid r hr).2] at hjet
  exact hjet

end NLS.Articles.KdVKdV2Frequencies
