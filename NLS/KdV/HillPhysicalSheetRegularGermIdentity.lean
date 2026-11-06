import NLS.KdV.HillDirichletSheetDetectorGerm
import NLS.ComplexAnalysis.AnalyticGermSign

/-! # Removing the physical sheet restriction before choosing a constant sign -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem eventuallyEq_or_neg_native_of_physical_sheet_regular_sq (n : ℕ+)
    (f g : Coeff 2 → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (f (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2=
        (g (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2) :
    f =ᶠ[𝓝 (0 : Coeff 2)] g ∨ f =ᶠ[𝓝 (0 : Coeff 2)] (fun u => -g u) := by
  obtain ⟨K,hKa,hKn,hKp⟩ := exists_hillDirichlet_sheet_detector_native_germ h0q h0r n
  have ha : AnalyticAt ℂ (fun u => K u*((f u)^2-(g u)^2)) 0 :=
    hKa.mul ((hf.pow 2).sub (hg.pow 2))
  have hp : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      K (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))*
        ((f (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2-
          (g (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2)=0 := by
    filter_upwards [he,hKp] with p he hKp
    by_cases hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)=0
    · rw [hKp hw,zero_mul]
    · rw [he hw,sub_self,mul_zero]
  have hz := eventuallyEq_native_of_physical_real_germ h0q h0r
    (fun u => K u*((f u)^2-(g u)^2)) (fun _ => 0) ha analyticAt_const hp
  have hsq := analytic_germ_cancel hKa ((hf.pow 2).sub (hg.pow 2)) hz hKn
  exact analytic_germ_eq_or_eq_neg_of_sq_eq hf hg
    (hsq.mono (fun _ hx => sub_eq_zero.mp hx))

end NLS.KdV
