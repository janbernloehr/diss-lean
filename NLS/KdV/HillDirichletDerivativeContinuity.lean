import NLS.KdV.HillAnalyticDirichletGardnerKernel

/-! # Continuity of the actual simple Dirichlet derivative at every labelled root -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual denominator in Dirichlet velocity residues is continuous
through every closed spectral gap as well as every open gap. -/
theorem continuous_hillDirichletCharacteristic_deriv_at_label (k : ℕ) (hk : 1≤k) :
    Continuous (fun p : RealPeriodOneHillPotential =>
      deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff p.val))
        (hillDirichletEnergy p.val p.property.1 p.property.2 k hk)) := by
  have ha := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) univ isOpen_univ
    analyticOnNhd_hillL2DirichletCharacteristic_joint
  have hd : Continuous (fun t : ℂ × Coeff 2 => deriv (hillL2DirichletCharacteristic t.2) t.1) :=
    continuous_iff_continuousAt.mpr (fun t => (ha t (mem_univ _)).continuousAt)
  have hμ : Continuous (fun p : RealPeriodOneHillPotential =>
      (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy k hk)
  have hP : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  simpa only [Function.comp_def] using! hd.comp (hμ.prodMk hP)

end NLS.KdV
