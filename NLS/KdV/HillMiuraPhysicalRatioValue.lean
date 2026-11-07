import NLS.KdV.HillHminusMiuraActionRatios

/-! Exact physical recovery for ANY supplied original Cauchy family
covering the actual Miura source. Both open and collapsed gaps retain
the intrinsic physical ratio. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

theorem miuraActionRatio_eq_physical (P : HillHminusPsiChart)
    {W : Set (CoeffPair 2)} (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ j : ℤ,
      P.miura.lift a (-j)=conj (P.miura.lift a j))
    (houtside : ∀ a∈P.miura.domain,hillHminusRadicand a (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
    (p : RealPeriodOneHillPotential) (hp : hillOriginalHminusSource p.val∈P.source)
    (hC : hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource p.val))∈
      ball C.discs.source.val C.discs.sourceRadius) (n : ℕ+) :
    P.miuraActionRatio C n (hillOriginalHminusSource p.val)=
      hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ) := by
  let F := fun a : PeriodOneHminusOne => hillMiuraDiagonal (P.miura.lift a)
  have hFa : AnalyticOnNhd ℂ F P.source := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha.1)
  let V := P.source∩F ⁻¹' ball C.discs.source.val C.discs.sourceRadius
  have hV : IsOpen V := hFa.continuousOn.isOpen_inter_preimage P.source_open isOpen_ball
  have hpV : hillOriginalHminusSource p.val∈V := ⟨hp,hC⟩
  have hpa := (P.miuraActionRatio_analyticAt_real C _ hp.1
    (hreal _ hp.1 (hillOriginalHminusSource_real p.val p.property.2)) hC n).1
  apply hillHminus_action_ratio_eq_of_physical_action_germ_at p n _ hpa.continuousAt
  have ht := (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto p
  filter_upwards [ht.eventually (hV.mem_nhds hpV)] with v hv
  exact P.miuraActionRatio_physical_factor C v hv.1 hreal (houtside _ hv.1.1) c hshift hv.2 n

end NLS.KdV.HillHminusPsiChart
