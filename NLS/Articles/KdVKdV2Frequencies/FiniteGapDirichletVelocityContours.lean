import NLS.Articles.KdVKdV2Frequencies.SmoothAbelianCoordinateMotion
import NLS.KdV.HillFiniteGapDirichletMoments

/-! # Actual finite-gap PDE velocity sums as Dirichlet contour coefficients

These use the actual normalized numerator and Dirichlet characteristic.
Identification with the article's F^3 and F^5 contours remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

variable (Q : C(AddCircle (2:ℝ),ℂ)) (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (N : ℕ)

def kdvDirichletVelocitySum : ℂ :=
  ∑ j ∈ Finset.range N,
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
      (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
        kdvDirichletVelocityCoefficient Q q (j+1)

def kdv2DirichletVelocitySum : ℂ :=
  ∑ j ∈ Finset.range N,
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
      (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
        kdv2DirichletVelocityCoefficient Q q (j+1)

theorem kdvDirichletVelocitySum_eq_residues :
    kdvDirichletVelocitySum Q q n hn N=
      ∑ j ∈ Finset.range N,
        (-2*(Q (0 : AddCircle (2:ℝ))+2*(hillDirichletEnergySequence q.val q.property.1 q.property.2 j : ℂ)))*
          (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
            (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)/
              deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
                (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)) := by
  unfold kdvDirichletVelocitySum
  apply Finset.sum_congr rfl
  intro j _hj
  rw [kdvDirichletVelocityCoefficient,dif_pos (by omega : 1≤j+1)]
  dsimp only [hillDirichletEnergySequence]
  ring

theorem kdv2DirichletVelocitySum_eq_residues :
    kdv2DirichletVelocitySum Q q n hn N=
      ∑ j ∈ Finset.range N,
        (-2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+
          3*Q (0 : AddCircle (2:ℝ))^2+
          4*(hillDirichletEnergySequence q.val q.property.1 q.property.2 j : ℂ)*Q (0 : AddCircle (2:ℝ))+
          8*(hillDirichletEnergySequence q.val q.property.1 q.property.2 j : ℂ)^2))*
          (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
            (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)/
              deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
                (hillDirichletEnergySequence q.val q.property.1 q.property.2 j)) := by
  unfold kdv2DirichletVelocitySum
  apply Finset.sum_congr rfl
  intro j _hj
  rw [kdv2DirichletVelocityCoefficient,dif_pos (by omega : 1≤j+1)]
  dsimp only [hillDirichletEnergySequence]
  ring

theorem kdvDirichletVelocitySum_eq_moments :
    kdvDirichletVelocitySum Q q n hn N=
      -2*Q (0 : AddCircle (2:ℝ))*hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 0-
        4*hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 1 := by
  rw [kdvDirichletVelocitySum_eq_residues]
  unfold hillDirichletResidueMoment
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [pow_zero,pow_one,one_mul]
  ring

theorem kdv2DirichletVelocitySum_eq_moments :
    kdv2DirichletVelocitySum Q q n hn N=
      (2*iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0-6*Q (0 : AddCircle (2:ℝ))^2)*
        hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 0-
      8*Q (0 : AddCircle (2:ℝ))*hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 1-
      16*hillDirichletResidueMoment q.val q.property.1 q.property.2 n hn N 2 := by
  rw [kdv2DirichletVelocitySum_eq_residues]
  unfold hillDirichletResidueMoment
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [pow_zero,pow_one,one_mul]
  ring

/-- Both actual velocity sums are exact normalized Dirichlet contour
coefficients on the same sufficiently large actual energy circles. -/
theorem eventually_kdvDirichletVelocitySums_eq_contours
    (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) :
    ∀ᶠ M : ℕ in atTop,
      kdvDirichletVelocitySum Q q n hn N=
        (2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(0,(centralCircleRadius M)^2),
          (-2*(Q (0 : AddCircle (2:ℝ))+2*w))*
            (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn w/
              hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) w) ∧
      kdv2DirichletVelocitySum Q q n hn N=
        (2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(0,(centralCircleRadius M)^2),
          (-2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+
            3*Q (0 : AddCircle (2:ℝ))^2+4*w*Q (0 : AddCircle (2:ℝ))+8*w^2))*
            (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn w/
              hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) w) := by
  have h1 := eventually_circleIntegral_hillFiniteGapDirichlet_analytic_test q.val q.property.1 q.property.2 n N hn hnN hclosed
    (fun w : ℂ => -2*(Q (0 : AddCircle (2:ℝ))+2*w))
    (fun _ _ => analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))
  have h2 := eventually_circleIntegral_hillFiniteGapDirichlet_analytic_test q.val q.property.1 q.property.2 n N hn hnN hclosed
    (fun w : ℂ => -2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+
      3*Q (0 : AddCircle (2:ℝ))^2+4*w*Q (0 : AddCircle (2:ℝ))+8*w^2))
    (fun _ _ => analyticAt_const.mul
      (((analyticAt_const.add analyticAt_const).add ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)).add
        (analyticAt_const.mul (analyticAt_id.pow 2))))
  have hne : (2*Real.pi*I : ℂ)≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  filter_upwards [h1,h2] with M hm1 hm2
  rw [hm1,hm2,← kdvDirichletVelocitySum_eq_residues,← kdv2DirichletVelocitySum_eq_residues]
  simp only [inv_mul_cancel_left₀ hne,and_self]

theorem eventually_fderiv_hillDirichletAbelianCoordinate_both_pde_contours
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ (N : ℕ), n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
    ∀ᶠ M : ℕ in atTop,
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
        (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        ((2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(0,(centralCircleRadius M)^2),
          (-2*(Q (0 : AddCircle (2:ℝ))+2*w))*
            (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn w/
              hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) w))*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) ∧
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
        (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        ((2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(0,(centralCircleRadius M)^2),
          (-2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+
            3*Q (0 : AddCircle (2:ℝ))^2+4*w*Q (0 : AddCircle (2:ℝ))+8*w^2))*
            (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn w/
              hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) w))*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
  dsimp only
  intro N hnN hclosed C hC hmatch
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have hjet := fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde Q hf hp hreal n hn N hclosed C hC hmatch
  change (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (kdvFourierDirection _ hf)=
      kdvDirichletVelocitySum Q q n hn N*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) ∧
    (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (kdv2FourierDirection _ hf)=
      kdv2DirichletVelocitySum Q q n hn N*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) at hjet
  filter_upwards [eventually_kdvDirichletVelocitySums_eq_contours Q q n hn N hnN hclosed] with M hM
  exact ⟨hjet.1.trans (congrArg (fun w : ℂ => w*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) hM.1),
    hjet.2.trans (congrArg (fun w : ℂ => w*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) hM.2)⟩

end NLS.Articles.KdVKdV2Frequencies
