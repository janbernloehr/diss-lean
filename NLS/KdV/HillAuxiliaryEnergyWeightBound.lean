import NLS.KdV.HillAuxiliaryMidpointSumLowerBound
import NLS.KdV.HillAbelianWeightNormBound
import NLS.ComplexAnalysis.QuadraticEnergyWeightBound

/-! The actual frequency weight is controlled by ORIGINAL quadratic
energy weights on ONE native complex neighborhood BEFORE ALL n.
The terminal is the ACTUAL AUXILIARY divisor; no gap is divided by. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalDirichlet_quadratic_energy_weight_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ D : ℝ, 0 < D ∧ ∀ y ∈ U, ∀ n : ℕ+,
        let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
        let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
        let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ) y
        ‖τ‖*(‖γ‖+‖μ-τ‖) ≤ D*(‖2*τ*γ‖+‖μ^2-τ^2-γ^2/4‖) := by
  obtain ⟨rT,aT,hrT,haT,hτlower⟩ := P.exists_uniform_source_frequency_midpoint_index_lower_bound q hq hr
  obtain ⟨rB,B,hrB,hB,hτupper⟩ := P.exists_uniform_source_frequency_midpoint_index_upper_bound q hq hr
  obtain ⟨rS,aS,hrS,haS,hsum⟩ := P.exists_uniform_physicalDirichletFrequency_add_midpoint_index_lower_bound q hq hr
  obtain ⟨Uw,hUw,hqw,_,R,hR,hweight⟩ := P.exists_local_abelianWeight_norm_bound q hq
  let U := ((Uw ∩ ball q rT) ∩ (ball q rB ∩ ball q rS)) ∩ P.physicalDirichletSource
  let K := B/aS
  let G := R/aT
  have hK : 0 ≤ K := div_nonneg hB haS.le
  have hG : 0 < G := div_pos hR haT
  refine ⟨U,((hUw.inter isOpen_ball).inter (isOpen_ball.inter isOpen_ball)).inter P.physicalDirichletSource_open,
    ⟨⟨⟨hqw,mem_ball_self hrT⟩,mem_ball_self hrB,mem_ball_self hrS⟩,P.real_mem_physicalDirichletSource q hq hr⟩,
    (fun _ h => h.2),1+K+K*G,by positivity,?_⟩
  intro y hy n
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
  let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ) y
  have hτK : ‖τ‖ ≤ K*‖μ+τ‖ := by
    calc
      _ ≤ B*(n:ℝ) := hτupper y hy.1.2.1 n
      _ = K*(aS*(n:ℝ)) := by dsimp only [K]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum y hy.1.2.2 n) hK
  have hτT := hτlower y hy.1.1.2 n
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.property
  have hτa : aT ≤ ‖τ‖ := by change aT*(n:ℝ) ≤ ‖τ‖ at hτT; nlinarith
  have hgcoord := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y)) ((n:ℕ):ℤ)
  have hw := hweight y hy.1.1.1
  have hgR : ‖γ‖ ≤ R := by dsimp only [γ]; linarith [norm_nonneg (P.physicalAbelianMidpointDisplacement y)]
  have hγG : ‖γ‖ ≤ G*‖τ‖ := by
    calc
      _ ≤ R := hgR
      _ = G*aT := by dsimp only [G]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hτa hG.le
  exact norm_frequency_weight_le_quadratic_energy_weight μ τ γ K G hK hG.le hτK hγG

end NLS.KdV.HillProductEquationPatch
