import NLS.KdV.HillPrimitiveMomentSeriesNeighborhood
import NLS.SequenceSpaces.PositiveSquaredGapMomentBound
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! Local l1 norm bounds for the actual weighted moment rows at
EVERY complex source of their common spectral neighborhood. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_normalizedWeightedSecondMoment_sum_bound (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ V ⊆ D.source ∧
      ∃ M : ℝ, ∀ a ∈ V, (∑' m : ℕ+, ‖P.normalizedWeightedSecondMoment D.ambient n a m‖) ≤ M := by
  obtain ⟨_,_,G,hG,hqG,R,hR,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (p := 2) (by simp) (by norm_num) (P.sourcePsi q) (by norm_num : (0:ℝ) < 1)
  let T := P.source ∩ P.sourcePsi ⁻¹' G
  have hT : IsOpen T := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hG
  let L := max D.threshold (2*(n:ℕ))
  have hfinite : {m : ℕ+ | (m:ℕ) ≤ L}.Finite :=
    (Set.finite_Iic L).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let s := hfinite.toFinset
  let F : PeriodOneHminusOne → ℝ := fun a => ∑ m ∈ s, ‖P.normalizedWeightedSecondMoment D.ambient n a m‖
  have hF : ContinuousAt F q := by
    apply tendsto_finsetSum
    intro m _
    exact (P.analytic_normalizedWeightedSecondMoment D n m q hq).continuousAt.norm
  have hnear : ∀ᶠ a in 𝓝 q, F a < F q+1 :=
    hF.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨B,hBsub,hB,hqB⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨(D.source ∩ T) ∩ B,(D.source_open.inter hT).inter hB,
    ⟨⟨hq,(D.subset hq).1,hqG⟩,hqB⟩,(fun a ha => ha.1.1),F q+1+3*D.constant*R^2,?_⟩
  intro a ha
  have he := Coeff.sum_norm_positive_weighted_le_of_squared_gap_tail
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)) n
    (fun m => (2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a)
    D.threshold D.constant D.constant_pos.le (fun m hm hmn => D.tail_bound a ha.1.1 n m hm hmn) s
    (fun m hm => by exact hfinite.mem_toFinset.mpr hm)
  have hg := (hgap (P.sourcePsi a) ha.1.2.2).1
  have hgn : 0 ≤ ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)‖ := norm_nonneg _
  have hg2 : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)‖^2 ≤ R^2 := by nlinarith
  have hFa : F a ≤ F q+1 := (hBsub ha.2).le
  have hC := D.constant_pos
  exact he.trans (add_le_add hFa (mul_le_mul_of_nonneg_left hg2 (by positivity : 0 ≤ 3*D.constant)))

end NLS.KdV.HillProductEquationPatch
