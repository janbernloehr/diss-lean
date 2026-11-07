import NLS.ComplexAnalysis.ScalarTaylorAlgebra
import NLS.ComplexAnalysis.AffinePencilJets

/-! Ordinary scalar Taylor coefficients, with product convolution and
the exact shift under multiplication by the spectral increment. -/
noncomputable section
open Complex PowerSeries
namespace NLS.ComplexAnalysis

def scalarTaylorCoefficient (n : ℕ) (f : ℂ → ℂ) : ℂ :=
  ((n.factorial:ℂ)⁻¹)*iteratedDeriv n f 0

theorem scalarTaylorCoefficient_eq_series {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesAt f p 0) (n : ℕ) :
    scalarTaylorCoefficient n f=PowerSeries.coeff n (scalarFormalTaylor p) := by
  rw [scalarTaylorCoefficient,← factorial_mul_coeff_scalarFormalTaylor hf n]
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem scalarTaylorCoefficient_mul {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    scalarTaylorCoefficient n (fun w => f w*g w)=
      ∑ i ∈ Finset.range (n+1), scalarTaylorCoefficient i f*scalarTaylorCoefficient (n-i) g := by
  have hfg := hf.mul hg
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  obtain ⟨r,hr⟩ := hfg
  change HasFPowerSeriesAt (fun w => f w*g w) r 0 at hr
  rw [scalarTaylorCoefficient_eq_series hr,scalarFormalTaylor_mul hp hq hr,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Finset.sum_congr rfl (fun i _ => by rw [scalarTaylorCoefficient_eq_series hp,scalarTaylorCoefficient_eq_series hq])

theorem scalarTaylorCoefficient_const_add_succ (c : ℂ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    scalarTaylorCoefficient (k+1) (fun w => c+w*f w)=scalarTaylorCoefficient k f := by
  rw [scalarTaylorCoefficient,iteratedDeriv_const_add (Nat.succ_pos k)]
  have h := normalized_iteratedDeriv_t_smul_succ hf k
  simpa only [smul_eq_mul,scalarTaylorCoefficient] using h

end NLS.ComplexAnalysis
