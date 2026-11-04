import NLS.KdV.HillCommonZeroRealAgreement

/-! A COMMON complex source ball BEFORE ALL numerator indices carries
analytic full-l2 ACTUAL zero sequences, with agreement on its ENTIRE real
slice and intrinsic numerator roots throughout its complex domain. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_actual_analytic_zero_sequences (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
      ∃ s : ℕ+ → PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
        ∀ n : ℕ+, AnalyticOnNhd ℂ (s n) (ball q ε) ∧
          s n q = hillHminusPsiZeroDisplacement n ⟨q,hr⟩ ∧
          (∀ y ∈ ball q ε, (s n y,y) ∈ P.inputDomain ∧ P.equation n (s n y,y) = 0 ∧
            (s n y,y) ∈ ball (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ρ ∧
            ∀ u : lp (fun _ : ℕ+ => ℂ) 2, (u,y) ∈ ball (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ρ →
              P.equation n (u,y) = 0 → u = s n y) ∧
          (∀ y ∈ ball q ε, ∀ hy : IsRealPeriodOneHminusOne y,
            s n y = hillHminusPsiZeroDisplacement n ⟨y,hy⟩) ∧
          ∀ m : ℕ+, m ≠ n → ∀ y ∈ ball q ε,
            hillHminusCanonicalPsi n (hillEnergySequenceZero m (s n y),y) = 0 := by
  obtain ⟨ρ,ε,hρ,hε,hbranches⟩ := P.exists_common_analytic_zero_sequence_ball q hq hr
  choose s hs hsq hgraph hreal using hbranches
  refine ⟨ρ,ε,hρ,hε,s,?_⟩
  intro n
  have hU : ∀ y ∈ ball q ε, (s n y,y) ∈ P.inputDomain := fun y hy => (hgraph n y hy).1
  have hF : ∀ y ∈ ball q ε, P.equation n (s n y,y) = 0 := fun y hy => (hgraph n y hy).2.1
  exact ⟨hs n,hsq n,hgraph n,
    P.common_analytic_sequence_real_agreement q hq hr ε hε n (s n) (hs n) hU hF (hreal n),
    fun m hmn => P.common_analytic_sequence_canonical_root q hq hr ε hε n (s n) (hs n) hU (hreal n) m hmn⟩

end NLS.KdV.HillProductEquationPatch
