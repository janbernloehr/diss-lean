import NLS.KdV.HillHminusMiuraActionMatching
import NLS.KdV.HillHminusSourceEnergyGap
import NLS.KdV.HillHminusPhysicalRatioIdentification
import NLS.ZakharovShabat.SourceNormalizedEnergyAction

/-! # Actual action ratios near every real rough Miura base

The weighted Dirac moment gives the Hill ratio without dividing by a
gap. Its native analyticity and positivity include closed gaps. Exact
physical actions and frequent opening identify the ORIGINAL physical
ratio throughout one rough neighborhood, with no L2 norm restriction.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

def miuraActionRatio (P : HillHminusPsiChart) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  C.normalizedEnergyActionRatio (n : ℤ) (hillMiuraDiagonal (P.miura.lift q))

theorem miuraActionRatio_analyticAt_real (P : HillHminusPsiChart)
    {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (q : PeriodOneHminusOne) (hq : q ∈ P.miura.domain)
    (hr : ∀ k : ℤ, P.miura.lift q (-k) = conj (P.miura.lift q k))
    (hC : hillMiuraDiagonal (P.miura.lift q) ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℕ+) :
    AnalyticAt ℂ (P.miuraActionRatio C n) q ∧
      0 < (P.miuraActionRatio C n q).re ∧ (P.miuraActionRatio C n q).im = 0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,hr⟩
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  have hleft := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast n.property)
  have hF : AnalyticAt ℂ (fun a => hillMiuraDiagonal (P.miura.lift a)) q :=
    (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic q hq)
  exact ⟨(C.normalizedEnergyActionRatio_analyticAt_of_real φ hC (n : ℤ) hleft).comp
    (f := fun a : PeriodOneHminusOne => hillMiuraDiagonal (P.miura.lift a)) hF,
    C.normalizedEnergyActionRatio_real_positive φ hC (n : ℤ) hleft⟩

theorem miuraActionRatio_physical_factor (P : HillHminusPsiChart)
    {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k) = conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
    (hC : hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val)) ∈
      ball C.discs.source.val C.discs.sourceRadius) (n : ℕ+) :
    (hillRealGapIntegral q.val q.property.1 q.property.2 (n : ℕ) 0 : ℂ) =
      (hillRealGapHalfLength q.val q.property.1 q.property.2 (n : ℕ) : ℂ)^2*
        P.miuraActionRatio C n (hillOriginalHminusSource q.val) := by
  let a := hillOriginalHminusSource q.val
  let u : PeriodOneRealL2 := ⟨P.miura.lift a,hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  obtain ⟨r,hr,_,hf⟩ := C.exists_ball_normalizedWeightedActions
    (sourceHigherActionAtlas (by norm_num) (by norm_num)) φ hC
  have hA := (hf (n : ℤ) 1).2 φ.val (mem_ball_self hr)
  obtain ⟨t,ht,hτ⟩ := sourceStandardRootMidpoint_real_positive (by norm_num) (by norm_num) φ (n : ℤ)
    (hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast n.property))
  have hne : sourceStandardRootMidpoint (by norm_num) (by norm_num) φ.val (n : ℤ) ≠ 0 := by
    rw [hτ]
    exact ofReal_ne_zero.mpr ht.ne'
  have he := C.normalizedEnergyActionRatio_factor (n : ℤ) φ.val _ hne hA
  have hδ : sourceStandardRootMidpoint (by norm_num) (by norm_num) φ.val (n : ℤ)*
      canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) (n : ℤ) =
      (hillRealGapHalfLength q.val q.property.1 q.property.2 (n : ℕ) : ℂ) := by
    have h := P.source_midpoint_mul_gap_eq_original_halfLength q hq hreal houtside c hshift n
    obtain ⟨hL,hR⟩ := canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num) φ.val
    change canonicalPeriodicMidpoint (by norm_num) (by norm_num)
      (periodOnePotential (sourcePhase φ.val)) (periodOnePotential_mem _) (n : ℤ)*
        canonicalPeriodicGap (by norm_num) (by norm_num)
          (periodOnePotential (sourcePhase φ.val)) (periodOnePotential_mem _) (n : ℤ) = _ at h
    dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap] at h
    rw [hL,hR] at h
    exact h
  rw [hδ] at he
  have hphysical := P.original_action_eq_twice_weighted_Dirac q hq hreal houtside c hshift n
  exact hphysical.trans he

theorem exists_local_Miura_action_ratios (P : HillHminusPsiChart)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ P.source) (hr0 : IsRealPeriodOneHminusOne q0)
    (hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k) = conj (P.miura.lift a k))
    (houtside : ∀ a ∈ P.miura.domain, hillHminusRadicand a (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2) :
    ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W,
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q0 ∈ V ∧ V ⊆ P.source ∧
        ∀ n : ℕ+, AnalyticAt ℂ (P.miuraActionRatio C n) q0 ∧
          0 < (P.miuraActionRatio C n q0).re ∧ (P.miuraActionRatio C n q0).im = 0 ∧
          ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ V →
            P.miuraActionRatio C n (hillOriginalHminusSource p.val) =
              hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (P.miura.lift a)
  let u : PeriodOneRealL2 := ⟨P.miura.lift q0,hreal q0 hq0.1 hr0⟩
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  obtain ⟨W,_,_,hfamily⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamily φ
  have hF : AnalyticOnNhd ℂ F P.source := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha.1)
  let V := P.source ∩ F ⁻¹' ball C.discs.source.val C.discs.sourceRadius
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage P.source_open isOpen_ball
  have hC0 : F q0 ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  refine ⟨W,C,V,hV,⟨hq0,hC0⟩,inter_subset_left,?_⟩
  intro n
  obtain ⟨ha,hpos,hIm⟩ := P.miuraActionRatio_analyticAt_real C q0 hq0.1 u.property hC0 n
  refine ⟨ha,hpos,hIm,?_⟩
  intro p hp
  have hpa := (P.miuraActionRatio_analyticAt_real C _ hp.1.1
    (hreal _ hp.1.1 (hillOriginalHminusSource_real p.val p.property.2)) hp.2 n).1
  apply hillHminus_action_ratio_eq_of_physical_action_germ_at p n _ hpa.continuousAt
  have ht := (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto p
  filter_upwards [ht.eventually (hV.mem_nhds hp)] with v hv
  exact P.miuraActionRatio_physical_factor C v hv.1 hreal (houtside _ hv.1.1) c hshift hv.2 n

end NLS.KdV.HillHminusPsiChart
