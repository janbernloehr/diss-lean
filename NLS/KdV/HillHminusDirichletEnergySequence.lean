import NLS.KdV.HillHminusOneDirichletCommonAnalytic
import NLS.SequenceSpaces.PositiveEnergyDisplacements

/-! # Native Hilbert normalized Dirichlet energies at every real Hminus-one source -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem exists_hillHminus_native_dirichlet_energy_sequence
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ E : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ E V ∧
      (∀ p ∈ V, ∀ n : ℕ+,
        hillHminusDirichlet p (((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*E p (n : ℤ)) = 0) ∧
      (∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        E p (n : ℤ) = ((hillHminusDirichletEnergy p hp n : ℂ)-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ)) ∧
      ∀ p : PeriodOneHminusOne, ∀ j : ℤ, j ≤ 0 → E p j = 0 := by
  obtain ⟨c,_hc,V,mu,d,hV,hqV,hd,_hmu,hroot,hphysical,hformula⟩ :=
    exists_hillHminusDirichlet_common_analytic_branches q hr
  let E := fun p => Coeff.positiveEnergyDisplacements c (d p)
  have he (p : PeriodOneHminusOne) (hp : p ∈ V) (n : ℕ+) :
      E p (n : ℤ) = (mu n p-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) := by
    rw [Coeff.positiveEnergyDisplacements_positive,← hformula p hp n]
  refine ⟨V,E,hV,hqV,fun p hp =>
    (Coeff.analyticOnNhd_positiveEnergyDisplacements c _ (mem_univ _)).comp (hd p hp),?_,?_,?_⟩
  · intro p hp n
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    rw [he p hp n,mul_div_cancel₀ _ hn,add_sub_cancel]
    exact hroot p hp n
  · intro p hp hpr n
    rw [he p hp n,hphysical p hp hpr n]
  · intro p j hj
    exact Coeff.positiveEnergyDisplacements_nonpositive c (d p) j hj

end NLS.KdV
