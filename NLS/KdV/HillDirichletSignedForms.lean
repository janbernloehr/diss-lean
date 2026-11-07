import NLS.KdV.HillH1PhysicalForms
import NLS.Fourier.UnitDirichletSignedTests
import NLS.FunctionalAnalysis.SignedPeriodicIntegral
import NLS.KdV.SingularDirichletPencil

/-! The full original Hill weak form restricted to SAME-PARITY extensions
of every native Dirichlet test. The original unit-period test insertion alone
does not give this identity for antiperiodic input vectors. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- Equal interval positions and a common parity give equality of the
ENTIRE original H1 products used by singular-potential multiplication. -/
theorem hillH1_product_signed_test_eq (r : ℤ)
    (G : FourierLebesgueSpace (2:ℝ) 1 2) (g h : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    h1Product G (unitDirichletSignedH1 r h) =
      h1Product (unitDirichletOriginalH1 g) (unitDirichletOriginalH1 h) := by
  apply singularHillContinuousDomainInclusion_injective
  rw [singularHillContinuousDomainInclusion_product,singularHillContinuousDomainInclusion_product]
  apply ContinuousMap.ext
  intro z
  obtain ⟨x,hx,rfl⟩ := AddCircle.eq_coe_Ioc z
  simp only [ContinuousMap.mul_apply,unitDirichletOriginalH1_representative]
  by_cases hx1 : x ≤ 1
  · rw [unitDirichletSignedH1_on_unit r h x ⟨hx.1.le,hx1⟩,← hsame x ⟨hx.1.le,hx1⟩]
  · have hxi : x-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith [hx.2]⟩
    have hGt := hG (x-1)
    have hgt := periodOneSobolevSynthesis_periodic g.val (x-1)
    have hht := periodOneSobolevSynthesis_periodic h.val (x-1)
    change unitDirichletRepresentative g (x-1+1) = unitDirichletRepresentative g (x-1) at hgt
    change unitDirichletRepresentative h (x-1+1) = unitDirichletRepresentative h (x-1) at hht
    simp only [sub_add_cancel] at hGt hgt hht
    rw [hGt,unitDirichletSignedH1_representative r h x ⟨hx.1.le,hx.2⟩,
      signedDouble_right _ _ (by linarith),← hsame (x-1) hxi,hgt,hht]
    calc
      _ = (wave r 1)^2*(unitDirichletRepresentative g (x-1)*unitDirichletRepresentative h (x-1)) := by ring
      _ = _ := by rw [wave_one_sq,one_mul]

/-- The same-parity native mass reduces to the UNNORMALIZED unit-interval
bilinear integral, with EVERY original H1 vector and full native test allowed. -/
theorem hillH1_mass_signed_test_integral (r : ℤ)
    (G : FourierLebesgueSpace (2:ℝ) 1 2) (h : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    singularHillPairing (singularHillDomainInclusion G) (unitDirichletSignedH1 r h) =
      ∫ x in (0:ℝ)..1, singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))*
        unitDirichletRepresentative h x := by
  rw [singularHillDomainInclusion_continuous_pairing]
  have hi : IntervalIntegrable (fun x : ℝ => singularHillContinuousDomainInclusion G
      (x : AddCircle (2:ℝ))*singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h)
        (x : AddCircle (2:ℝ))) volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact ((singularHillContinuousDomainInclusion G).continuous.comp continuous_quotient_mk').mul
      ((singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h)).continuous.comp
        continuous_quotient_mk')
  rw [half_integral_mul_of_common_sign _ _ (wave r 1) (wave_one_sq r) hG
    (unitDirichletSignedH1_translate_one r h) hi]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  dsimp only
  rw [unitDirichletSignedH1_on_unit r h x hxi]

/-- For a common sign, the free native weak form reduces to its exact
unit-interval derivative product. The H1 derivatives remain actual derivatives. -/
theorem hillH1_laplacian_signed_integral (r : ℤ)
    (F H : FourierLebesgueSpace (2:ℝ) 1 2)
    (hF : ∀ x : ℝ, singularHillContinuousDomainInclusion F ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion F (x : AddCircle (2:ℝ)))
    (hH : ∀ x : ℝ, singularHillContinuousDomainInclusion H ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion H (x : AddCircle (2:ℝ))) :
    singularHillPairing (singularHillLaplacian F) H =
      ∫ x in (0:ℝ)..1,
        deriv (fun y : ℝ => singularHillContinuousDomainInclusion F (y : AddCircle (2:ℝ))) x*
          deriv (fun y : ℝ => singularHillContinuousDomainInclusion H (y : AddCircle (2:ℝ))) x := by
  rw [singularHillLaplacian_continuous_pairing]
  apply half_integral_mul_of_common_sign _ _ (wave r 1) (wave_one_sq r)
    (deriv_translate_one_of_multiplier _ _ hF) (deriv_translate_one_of_multiplier _ _ hH)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 2)).mpr
    ((memLp_deriv_sobolevSynthesis (sobolevCoefficients 1 2 F)).integrable_mul
      (memLp_deriv_sobolevSynthesis (sobolevCoefficients 1 2 H)))

/-- The ACTUAL native free weak forms agree on ALL Dirichlet tests
when the original interval representative is retained. -/
theorem hillH1_laplacian_signed_test_eq (r : ℤ)
    (G : FourierLebesgueSpace (2:ℝ) 1 2) (g h : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    singularHillPairing (singularHillLaplacian G) (unitDirichletSignedH1 r h) =
      singularHillPairing (singularHillLaplacian (unitDirichletOriginalH1 g))
        (unitDirichletOriginalH1 h) := by
  have hunit (v : UnitDirichletH1) (x : ℝ) :
      singularHillContinuousDomainInclusion (unitDirichletOriginalH1 v) ((x+1:ℝ) : AddCircle (2:ℝ)) =
        wave 0 1*singularHillContinuousDomainInclusion (unitDirichletOriginalH1 v) (x : AddCircle (2:ℝ)) := by
    simp only [unitDirichletOriginalH1_representative,wave_zero,one_mul]
    exact periodOneSobolevSynthesis_periodic v.val x
  rw [hillH1_laplacian_signed_integral r G _ hG (unitDirichletSignedH1_translate_one r h),
    hillH1_laplacian_signed_integral 0 _ _ (hunit g) (hunit h)]
  have hf := ae_deriv_eq_of_eqOn_Icc (a := 0) (b := 1) (f := fun x : ℝ => singularHillContinuousDomainInclusion G
      (x : AddCircle (2:ℝ))) (g := fun x : ℝ =>
        singularHillContinuousDomainInclusion (unitDirichletOriginalH1 g) (x : AddCircle (2:ℝ)))
    (fun x hx => by dsimp only;rw [unitDirichletOriginalH1_representative];exact (hsame x hx).symm)
  have hh := ae_deriv_eq_of_eqOn_Icc (a := 0) (b := 1) (f := fun x : ℝ => singularHillContinuousDomainInclusion
      (unitDirichletSignedH1 r h) (x : AddCircle (2:ℝ)))
    (g := fun x : ℝ => singularHillContinuousDomainInclusion (unitDirichletOriginalH1 h) (x : AddCircle (2:ℝ)))
    (fun x hx => by dsimp only;rw [unitDirichletSignedH1_on_unit r h x hx,unitDirichletOriginalH1_representative])
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [hf,hh] with x hfx hhx
  rw [hfx,hhx]

/-- FULL native Hill-to-Dirichlet operator compatibility, tested against
EVERY original Dirichlet H1 vector using its SAME-PARITY extension.
This includes antiperiodic G and arbitrary complex singular potentials. -/
theorem singularDirichletOperator_signed_test (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (r : ℤ) (G : FourierLebesgueSpace (2:ℝ) 1 2) (g h : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    singularDirichletOperator q g h = singularHillPairing (singularHillOperator q G)
      (unitDirichletSignedH1 r h) := by
  change singularHillPairing (singularHillLaplacian (unitDirichletOriginalH1 g)+
    hminusOneMultiplication q (unitDirichletOriginalH1 g)) (unitDirichletOriginalH1 h) =
      singularHillPairing (singularHillLaplacian G+hminusOneMultiplication q G) (unitDirichletSignedH1 r h)
  rw [singularHillPairing_add_left,singularHillPairing_add_left,
    hillH1_laplacian_signed_test_eq r G g h hG hsame]
  congr 1
  simp only [singularHillPairing,hminusOneMultiplication_apply,hminusOneProduct_duality]
  rw [hillH1_product_signed_test_eq r G g h hG hsame]

end NLS.KdV
