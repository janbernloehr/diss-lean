import NLS.ComplexAnalysis.BanachC1ImplicitDerivative
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! Exact scalar implicit-root derivatives in a complex Banach parameter.
Only the actual local root equation and first derivatives are used. -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem implicitScalarRoot_fderiv_apply (F : ℂ × A → ℂ) (s : A → ℂ) (x h : A)
    (hF : DifferentiableAt ℂ F (s x,x)) (hs : DifferentiableAt ℂ s x)
    (hzero : ∀ᶠ q in 𝓝 x, F (s q,q) = 0)
    (hne : (fderiv ℂ F (s x,x)) (1,0) ≠ 0) :
    (fderiv ℂ s x) h =
      -(fderiv ℂ (fun q => F (s x,q)) x) h / (fderiv ℂ F (s x,x)) (1,0) := by
  let L := fderiv ℂ F (s x,x)
  let a := (fderiv ℂ s x) h
  have hb : L (a,h) = 0 := implicitBanachRoot_fderiv_balance F s x hF hs hzero h
  have hdecomp : (a,h) = a • ((1:ℂ),(0:A))+(0,h) := by ext <;> simp
  rw [hdecomp,map_add,map_smul] at hb
  rw [fderiv_source_section_eq_joint F (s x) x hF,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
  apply (eq_div_iff hne).2
  exact eq_neg_of_add_eq_zero_left hb

end NLS.ComplexAnalysis
