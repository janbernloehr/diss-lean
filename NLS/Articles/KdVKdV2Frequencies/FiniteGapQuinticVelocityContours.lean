import NLS.KdV.HillQuinticFrequencyContourComparison
import NLS.KdV.HillFiniteGapDirichletNormalization
import NLS.Articles.KdVKdV2Frequencies.FiniteGapDirichletVelocityContours
/-! # Exact actual finite-gap KdV2 contours with the physical mass correction -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

theorem eventually_kdv2_renormalized_dirichlet_contour
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
    ∀ᶠ M : ℕ in atTop,
      (-16/(I*Real.pi) : ℂ)*(∮ E in C(0,(centralCircleRadius M)^2),
        (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)*(hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E))=
      kdv2DirichletVelocitySum Q q n hn N-20*(2*(n:ℂ)*Real.pi)*
        classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ))) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let H := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))
  let P : ℂ → ℂ := fun E => (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)
  have hP : AnalyticOnNhd ℂ P univ := by intro E _hE;dsimp only [P];fun_prop
  have hS0 := hillFiniteGapDirichletResidueMoment_zero_order_eq Q q.property.1 q.property.2 hreal hf hp hmean n N hn hnN hclosed
  have hsum : -32*(∑ j∈Finset.range N, P (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)*
      (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
        (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)/
        deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
          (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)))=
      kdv2DirichletVelocitySum Q q n hn N+20*H*
        hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 0 := by
    rw [kdv2DirichletVelocitySum_eq_residues]
    unfold hillDirichletResidueMoment
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [P,H,pow_zero,one_mul,iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  rw [hS0] at hsum
  filter_upwards [eventually_circleIntegral_hillFiniteGapDirichlet_analytic_test q.val q.property.1 q.property.2 n N hn hnN hclosed P hP] with M hM
  change (-16/(I*Real.pi) : ℂ)*(∮ E in C(0,(centralCircleRadius M)^2),
    P E*(hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E))=_
  rw [hM,← mul_assoc]
  have hc : (-16/(I*Real.pi) : ℂ)*(2*Real.pi*I)= -32 := by field_simp;ring
  rw [hc,hsum]
  dsimp only [H]
  ring

theorem tendsto_kdv2_quintic_frequency_contour
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
    Tendsto (fun M : ℕ => (-16/(I*Real.pi) : ℂ)*
      (∮ E in C(0,(centralCircleRadius M)^2),
        hillL2OddKernel q.val 2 (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn) E)) atTop
      (𝓝 (kdv2DirichletVelocitySum Q q n hn N-20*(2*(n:ℂ)*Real.pi)*
        classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ))))) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let f := hillL2OddKernel q.val 2 (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn)
  let g := fun E => (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)*(hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E)
  let a : ℂ := -16/(I*Real.pi)
  have herror := (tendsto_hillFiniteGap_quintic_contour_sub_dirichlet Q q.property.1 q.property.2
    hreal hf hp hmean n N hn hclosed).const_mul a
  have hlim : Tendsto (fun M : ℕ => a*((∮ E in C(0,(centralCircleRadius M)^2), f E)-
      (∮ E in C(0,(centralCircleRadius M)^2), g E))) atTop (𝓝 0) := by
    simpa only [mul_zero] using herror
  have heq : (fun M : ℕ => a*(∮ E in C(0,(centralCircleRadius M)^2), g E)) =ᶠ[atTop]
      (fun _ => kdv2DirichletVelocitySum Q q n hn N-20*(2*(n:ℂ)*Real.pi)*
        classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)) )) :=
    eventually_kdv2_renormalized_dirichlet_contour Q hreal hf hp hmean n hn N hnN hclosed
  have hg : Tendsto (fun M : ℕ => a*(∮ E in C(0,(centralCircleRadius M)^2), g E)) atTop
      (𝓝 (kdv2DirichletVelocitySum Q q n hn N-20*(2*(n:ℂ)*Real.pi)*
        classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ))))) :=
    tendsto_const_nhds.congr' heq.symm
  have hh := hlim.add hg
  simp only [zero_add] at hh
  convert hh using 1
  funext M
  ring
theorem exists_kdv2DirichletVelocity_quintic_contour_identity
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
      CircleIntegrable (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^5*
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
          hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E) 0 r ∧
      kdv2DirichletVelocitySum Q q n hn N-20*(2*(n:ℂ)*Real.pi)*
        classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))=(-16/(I*Real.pi) : ℂ)*
        (∮ E in C(0,r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^5*
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let P := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let f := hillL2OddKernel q.val 2 P
  let a : ℂ := -16/(I*Real.pi)
  have hfg : HillFiniteGap q.val q.property.1 q.property.2 := by
    apply (hillFiniteGap_iff_collapsed_tail q.val q.property.1 q.property.2).2
    refine ⟨N+1,?_⟩
    intro k hk hk1
    have he := hclosed k hk1 (by omega)
    dsimp only [hillRealGapHalfLength] at he
    linarith
  obtain ⟨R,hR,_ha,hperiod⟩ := HillFiniteGap.exists_odd_exterior_and_periods q.val q.property.1 q.property.2 hfg 2 n hn
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
  have hlim := tendsto_kdv2_quintic_frequency_contour Q hreal hf hp hmean n hn N hnN hclosed
  have hconst := hlim.congr' heq
  exact tendsto_nhds_unique hconst tendsto_const_nhds

end NLS.Articles.KdVKdV2Frequencies
