import NLS.KdV.HillHminusL2MiuraRatioAnalytic
import NLS.KdV.HillMiuraPhysicalRatioValue

/-! Actual original physical action ratios have quantitative inverse-index
error on ONE original complex L2 neighborhood, with common analytic
representatives and physical recovery including closed gaps. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem exists_native_l2_physical_actionRatio_decay
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ N : ℕ, ∃ K : ℝ, ∃ R : ℕ+ → WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → ℂ,
        0≤K ∧ ∀ n : ℕ+, N≤(n:ℕ) → AnalyticOnNhd ℂ (R n) U ∧
          (∀ a∈U, (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*R n a-1‖≤K) ∧
          ∀ p : RealPeriodOneHillPotential, ∀ a∈U,
            hillOriginalHminusSource p.val=periodOneSobolevImageInclusion 1 (by norm_num) a →
            R n a=hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨P,c,_hc,hshift,hqP,hreal,houtside,_hlabels,_H,hstrong⟩ :=
    exists_hillHminus_retained_Miura_eta_chart (L q) hr
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource
    ⟨P.miura.lift (L q),(periodOneL2Conjugation_fixed_iff _).mp (hreal _ hqP.1.1 hr)⟩
  obtain ⟨W,_hW,_hRW,hfamily⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamily φ
  have hCq : hillMiuraDiagonal (P.miura.lift (L q))∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨V,hV,hqV,hVP,N,K,hK,hd⟩ := P.exists_native_l2_analytic_miura_actionRatio_decay hstrong C q hqP
    (hreal _ hqP.1.1 hr) hCq
  let F := fun a => hillMiuraDiagonal (P.miura.lift (L a))
  have hFa : AnalyticOnNhd ℂ F V := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp ((P.miura.lift_analytic _ (hVP a ha).1.1).comp (L.analyticAt a))
  let U := V∩F ⁻¹' ball C.discs.source.val C.discs.sourceRadius
  refine ⟨U,hFa.continuousOn.isOpen_inter_preimage hV isOpen_ball,⟨hqV,hCq⟩,
    N,K,(fun n a => P.miuraActionRatio C n (L a)),hK,?_⟩
  intro n hn
  refine ⟨((hd n hn).1).mono inter_subset_left,(fun a ha => (hd n hn).2 a ha.1),?_⟩
  intro p a ha he
  change P.miuraActionRatio C n (L a)=_
  rw [←he]
  exact P.miuraActionRatio_eq_physical C
    (fun b hb hbr => (periodOneL2Conjugation_fixed_iff _).mp (hreal b hb hbr))
    houtside c hshift p (he ▸ (hVP a ha.1).1) (he ▸ ha.2) n

end NLS.KdV
