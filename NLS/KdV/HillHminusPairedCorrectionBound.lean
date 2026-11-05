import NLS.KdV.HillHminusPairedSourceCorrection
import NLS.ZakharovShabat.SourceAngularOriginalBetaUniformNorm

/-! # A common bound before every actual paired rough phase correction -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillHminusPsiChart

theorem exists_local_uniform_sourcePairedBetaCorrection_bound (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ B : ℝ, 0 < B ∧ ∀ a∈U, ∀ n : ℕ+, ‖P.sourcePairedBetaCorrection n a‖ ≤ B := by
  obtain ⟨V,hV,hqV,hVW,B,hB,hbound⟩ :=
    H.exists_local_uniform_absolute_beta_bound (P.dirichletSource q) hq.2
  let U := P.sourceBetaDomain ∩ P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  refine ⟨U,hc.isOpen_inter_preimage P.sourceBetaDomain_open hV,⟨hq,hqV⟩,
    inter_subset_left,3*B,by positivity,?_⟩
  intro a ha n
  have hs := hbound _ ha.2 ((n : ℕ) : ℤ)
  have hterm (m : ℤ) :
      ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) ((n : ℕ) : ℤ)
        P.family.roots (P.dirichletSource a) m‖ ≤ B :=
    (hs.1.le_tsum m (fun _ _ => norm_nonneg _)).trans hs.2
  have hcB : ‖P.sourceBetaCorrection (n : ℕ) a‖ ≤ B :=
    (norm_tsum_le_tsum_norm hs.1).trans hs.2
  have hn0 : (0 : ℤ)≠(n : ℕ) := by have := n.pos; omega
  have hnneg : -((n : ℕ) : ℤ)≠(n : ℕ) := by have := n.pos; omega
  have hzero := hterm 0
  have hneg := hterm (-((n : ℕ) : ℤ))
  simp only [sourceAngularBetaSeriesTerm,if_neg hn0] at hzero
  simp only [sourceAngularBetaSeriesTerm,if_neg hnneg] at hneg
  rw [P.sourcePairedBetaCorrection_eq H n a ha.1]
  exact ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
    (by linarith)

end NLS.KdV.HillHminusPsiChart
