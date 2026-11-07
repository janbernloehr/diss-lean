import NLS.Poisson.GardnerHamiltonianDirection
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! Chain rules for the literal scalar Gardner bracket: moving
spectral evaluation and the determinant-one multiplier trace. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem hminusGardnerBracket_moving_spectral_right
    (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (T : ℂ × WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (s : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hT : DifferentiableAt ℂ T (s q,q)) (hs : DifferentiableAt ℂ s q) :
    hminusGardnerBracket F (fun p => T (s p,p)) q=
      hminusGardnerBracket F (fun p => T (s q,p)) q+
        deriv (fun E => T (E,q)) (s q)*hminusGardnerBracket F s q := by
  change gardnerCotangentBivector (fderiv ℂ F q) (fderiv ℂ (fun p => T (s p,p)) q)=_
  rw [NLS.ComplexAnalysis.fderiv_moving_spectral_parameter T s q hT hs,map_add,map_smul]
  rfl

theorem hminusGardnerBracket_inv_add_right
    (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hG : DifferentiableAt ℂ G q) (hne : G q ≠ 0) :
    hminusGardnerBracket F (fun p => (G p)⁻¹+G p) q=
      (1-((G q)^2)⁻¹)*hminusGardnerBracket F G q := by
  have hN := hG.hasFDerivAt
  have hI := (hasFDerivAt_inv hne).comp q hN
  have hd := (hI.add hN).fderiv
  change fderiv ℂ (fun p => (G p)⁻¹+G p) q=_ at hd
  have he : fderiv ℂ (fun p => (G p)⁻¹+G p) q=(1-((G q)^2)⁻¹) • fderiv ℂ G q := by
    rw [hd]
    ext h
    simp only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,smul_apply,smul_eq_mul]
    ring
  change gardnerCotangentBivector (fderiv ℂ F q) (fderiv ℂ (fun p => (G p)⁻¹+G p) q)=_
  rw [he,map_smul]
  rfl

end NLS.Poisson
