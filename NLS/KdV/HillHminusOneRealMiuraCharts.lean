import NLS.KdV.HillHminusOneWeakFormReality
import NLS.SequenceSpaces.PeriodOneRealMiuraCharts

/-! # Actual analytic Hill charts that preserve physical realness -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillHminus_real_Miura_chart (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ C : HillHminusMiuraChart, q ∈ C.domain ∧ ∃ c : ℝ, 0 < c ∧ C.energyShift = (c : ℂ)^2 ∧
      ∀ p ∈ C.domain, IsRealPeriodOneHminusOne p → star (C.physicalProfile p) = C.physicalProfile p := by
  obtain ⟨m,U,hU,hq,u,hu,himage,hreal⟩ := exists_real_periodOneMiura_energyChart q
    ((periodOneHminusConjugation_fixed_iff q).mpr hr)
  let c : ℝ := ((m : ℝ)+1)/2
  let C : HillHminusMiuraChart := ⟨U,hU,(c : ℂ)^2,u,hu,by
    intro p hp
    simpa only [c,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat] using! himage p hp⟩
  refine ⟨C,hq,c,by dsimp [c]; positivity,rfl,?_⟩
  intro p hp hpr
  have hfixed := hreal p hp ((periodOneHminusConjugation_fixed_iff p).mpr hpr)
  exact unitL2Synthesis_star_eq_self_of_real _ ((periodOneL2Conjugation_fixed_iff _).mp hfixed)

end NLS.KdV
