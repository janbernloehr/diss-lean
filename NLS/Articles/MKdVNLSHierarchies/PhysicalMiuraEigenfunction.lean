import NLS.Articles.MKdVNLSHierarchies.PhysicalMiuraMatrix
import NLS.MKdV.MiuraTransformedColumns

/-! # Lemma 2 for arbitrary interval eigenfunctions at every original H1 source

The input function is only required to have absolutely continuous components
and satisfy the actual physical eigen-equation almost everywhere. No periodic
boundary condition or constructed-solution hypothesis is imposed on it.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma2_h1_transformed_matrix (a : ScalarDomain 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    miuraTransformedColumns
      (classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z t =
        miuraTransferMatrix a z t*classicalFundamentalMatrix
          (classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z t := by
  apply miuraTransformedColumns_eq_gauge_mul _
    (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)))
  intro s
  change (periodOneMiuraCurve a s,periodOneMiuraCurve a s) = _
  simp only [periodOneMiuraCurve_apply]

theorem lemma2_h1_transformed_determinant (a : ScalarDomain 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    (miuraTransformedColumns
      (classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z t).det = -2*z := by
  rw [lemma2_h1_transformed_matrix,Matrix.det_mul,lemma2_transfer_matrix_determinant,
    det_classicalFundamentalMatrix,mul_one]

/-- The full scalar intertwining at the original complex H1 source, in the
larger arbitrary AC eigenfunction class, including the zero parameter. -/
theorem lemma2_h1_arbitrary_eigenfunction (a : ScalarDomain 2) (z : ℂ)
    (f : ℝ → ℂ × ℂ)
    (hf₁ : AbsolutelyContinuousOnInterval (fun x => (f x).1) 0 1)
    (hf₂ : AbsolutelyContinuousOnInterval (fun x => (f x).2) 0 1)
    (he : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 →
      physicalOperator
        (fun y => (periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)),
          periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)))) f x = z • f x) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0:ℝ) 1 →
      -deriv (deriv (fun y => (f y).1+I*(f y).2)) x+
        miuraPotential (fun y => periodOneSobolevSynthesis a (y : AddCircle (2:ℝ))) x*
          ((f x).1+I*(f x).2) = z^2*((f x).1+I*(f x).2) := by
  let Φ := classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)
  let u : ℝ → ℂ := fun y => periodOneSobolevSynthesis a (y : AddCircle (2:ℝ))
  have hΦ (t : Icc (0:ℝ) 1) : Φ t = (u t,u t) := by
    change (periodOneMiuraCurve a t,periodOneMiuraCurve a t) = (u t,u t)
    simp only [periodOneMiuraCurve_apply,u]
  have he' : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 → physicalOperator (extend Φ) f x = z • f x := by
    filter_upwards [he] with x hxe hx
    have hφ : extend Φ x = (u x,u x) := by rw [extend_coe _ ⟨x,hx⟩,hΦ ⟨x,hx⟩]
    simpa only [physicalOperator,hφ] using hxe hx
  filter_upwards [NLS.FunctionalAnalysis.ae_differentiableAt_complex
    (absolutelyContinuous_periodOneSobolevSynthesis a)] with x hxd hx
  have hxi : x ∈ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ⟨hx.1.le,hx.2.le⟩
  exact miura_equation_of_ac_physical_eigenfunction Φ u z f hΦ hf₁ hf₂ he' x hx (hxd hxi)

end NLS.Articles.MKdVNLSHierarchies
