import NLS.ZakharovShabat.SourceBirkhoffOriginalFormula
import NLS.ZakharovShabat.SourceTheorem11_2

/-!
# Original rectangular coordinates through collapsed gaps

A common restriction preserves the original root family. The coordinates
are analytic at every complex gap and their squared radius is twice the
original indexed action.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A common restriction keeps the original root family and indexed actions. -/
theorem exists_original_birkhoff_coordinate_domain (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceBirkhoffX hp hp1 n s) V ∧
        AnalyticOnNhd ℂ (sourceBirkhoffY hp hp1 n s) V) ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        (sourceBirkhoffX hp hp1 n s ψ)^2+(sourceBirkhoffY hp hp1 n s ψ)^2 = 2*sourceIndexedAction hp hp1 n ψ := by
  have A : SourceLemma11_1Data hp hp1 W₀ := H.previous.previous.psi.previous.previous.previous.previous
  obtain ⟨U,hU,hrU,A⟩ := A.normalizedActions
    (H.original_theta_common_domain.real_subset.trans H.previous.previous.subset)
  refine ⟨W ∩ U,H.original_theta_common_domain.source_open.inter hU,
    (fun ψ hψ => ⟨H.original_theta_common_domain.real_subset hψ,hrU hψ⟩),inter_subset_left,?_,?_⟩
  · intro n
    constructor
    · intro ψ hψ
      exact (analyticAt_sourceBirkhoffXY hp hp1 n s ψ (A.root_analytic n ψ hψ.2)
        (fun sign => H.gapWeightedEta_original_analytic n sign ψ hψ.1)
        (H.beta_original_series.analytic_correction n ψ hψ.1)).1
    · intro ψ hψ
      exact (analyticAt_sourceBirkhoffXY hp hp1 n s ψ (A.root_analytic n ψ hψ.2)
        (fun sign => H.gapWeightedEta_original_analytic n sign ψ hψ.1)
        (H.beta_original_series.analytic_correction n ψ hψ.1)).2
  · intro ψ hψ n
    obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ.1
    have hprod := sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
      ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
    have hf := A.factorization ψ hψ.2 n
    rw [(A.agreement ψ hψ.2 n).2] at hf
    have hx := sourceBirkhoffX_sq_add_Y_sq hp hp1 n s ψ
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hprod) (A.root_sq ψ n)
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hf)
    rw [← (A.agreement ψ hψ.2 n).2] at hx
    exact hx

end SourceLemma12_12Data
end NLS.ZakharovShabat
