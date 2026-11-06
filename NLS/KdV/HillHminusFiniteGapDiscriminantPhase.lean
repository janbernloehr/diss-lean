import NLS.KdV.HillMiuraGroundFiniteGap
import NLS.KdV.HillMiuraTraceOrder
import NLS.ZakharovShabat.SourceFiniteGapDiscriminantPhase
import NLS.ComplexAnalysis.AnalyticPhaseEnergyShift

/-! # The actual normalized analytic phase of a rough finite-gap Hill trace -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- Every real mean-zero rough Hill potential with eventually closed gaps
has an actual analytic inversion phase at infinity. Its existence follows
from the ground Miura factor and the literal translated discriminant. -/
theorem exists_hillHminus_finiteGap_discriminant_phase
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hclosed : ∀ n : ℕ, N ≤ n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1)) :
    ∃ T : ℝ, 0 < T ∧ ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = 0 ∧
      ∀ z : ℂ, T < ‖z‖ → 2*cosh (-I*z+B z⁻¹) = hillHminusDiscriminant q (z^2) := by
  obtain ⟨u,_hu,hi,_hn,hf,_hbound⟩ :=
    exists_finiteGap_ground_factor_with_energy_bound q hq hm N hN hclosed
  obtain ⟨R,_hR,A,hA,hA0,hrep⟩ :=
    exists_sourceFiniteGap_discriminant_phase (by simp) (by norm_num) (hillMiuraRealSource u) hf
  obtain ⟨T,hT,B,hB,hB0,hshift⟩ :=
    exists_analytic_phase_energy_shift (-hillHminusLowestRealRoot q hq : ℂ) A hA hA0 R
  refine ⟨T,hT,B,hB,hB0,?_⟩
  intro z hz
  obtain ⟨ζ,hζ,henergy,hphase⟩ := hshift z hz
  rw [hphase,hrep ζ hζ]
  have he : ζ^2-(-hillHminusLowestRealRoot q hq : ℂ) = z^2 := by rw [henergy]; ring
  have ht := hillHminusDiscriminant_shifted_miura_square q u.val
    (-hillHminusLowestRealRoot q hq : ℂ) ζ (by simpa only [ofReal_neg] using hi)
  rw [he] at ht
  exact ht.symm

end NLS.KdV
