import NLS.KdV.HillProductEquationFamilyCompact
import NLS.KdV.HillAffineEnergyPeriods
import NLS.KdV.HillPeriodWeightLimit
import NLS.KdV.HillRealEnergyGapDataPlacement
import NLS.SequenceSpaces.LpOperatorBasisExt

/-! Every escaping-index operator-norm limit of actual real Hill period
Jacobians has the EXACT full-energy-product physical period entries at
an original real gap selection. That selection solves ALL full periods.
Invertibility of these identified full-product operators is not assumed. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def canonicalPeriodCircle (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (k : ℤ) :
    SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) k :=
  P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 k (P.centers k) (P.radii k) (P.radii_pos k) (P.discs_eq k)

def fullEnergyPeriodJacobianEntries (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) : Prop :=
  ∀ m r : ℕ+, T (lp.single 2 r 1) m = (2*Real.pi:ℂ)*hillEnergyFullProductPeriodColumn r
    (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q) (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d


theorem fullEnergyPeriodJacobian_apply (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : P.fullEnergyPeriodJacobianEntries q hq d T) (m : ℕ+) (h : lp (fun _ : ℕ+ => ℂ) 2) :
    T h m = (2*Real.pi:ℂ)*fderiv ℂ
      (hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q)
        (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ))) d h := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  let A : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).comp T
  let L : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ := (2*Real.pi:ℂ) • fderiv ℂ (hillEnergyFullProductFixedPeriod (B.shift:ℂ) (P.sourcePsi q)
    (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ))) d
  have heq : A = L := by
    apply LpSequence.continuousLinearMap_eq_of_single (by norm_num)
    intro r
    dsimp only [A,L]
    rw [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul]
    have hc := fderiv_hillEnergyFullProductFixedPeriod_coordinate r (B.shift:ℂ) (P.sourcePsi q) hreal
      (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d
    simpa only [lp.evalCLM,LinearMap.mkContinuous_apply,lp.evalₗ_apply] using! (hT m r).trans (congrArg (fun w : ℂ => (2*Real.pi:ℂ)*w) hc.symm)
  exact congrArg (fun F : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ => F h) heq

theorem sequenceJacobian_actual_real_escaping_entry_tendsto (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto (fun j => hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩) atTop (𝓝 d))
    (m r : ℕ+) :
    Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q) (lp.single 2 r 1) m)
      atTop (𝓝 ((2*Real.pi:ℂ)*hillEnergyFullProductPeriodColumn r
        (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q) (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d)) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  have hc := tendsto_hillEnergyProductPeriodColumn_escaping r (B.shift:ℂ) (P.sourcePsi q) hreal
    (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) n hn _ d hd
  apply ((tendsto_hillPeriodEquationWeight_escaping n hn m).mul hc).congr'
  filter_upwards [eventually_fixed_pnat_ne_escaping n hn m] with j hj
  rw [P.sequenceJacobian_coordinate (n j) m r _ q (P.actual_real_graph_mem q hq hr (n j))
    (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) rfl rfl,if_neg hj]

theorem fullEnergyPeriodJacobianEntries_of_escaping_limit (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto (fun j => hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩) atTop (𝓝 d))
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T)) :
    P.fullEnergyPeriodJacobianEntries q hq d T := by
  intro m r
  have hpoint := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).continuous.tendsto _).comp
    (((ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ+ => ℂ) 2) (lp.single 2 r 1)).continuous.tendsto T).comp hT)
  exact tendsto_nhds_unique hpoint (P.sequenceJacobian_actual_real_escaping_entry_tendsto q hq hr n hn d hd m r)

theorem fullEnergyPeriod_zero_of_escaping_actual_data (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto (fun j => hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩) atTop (𝓝 d)) (m : ℕ+) :
    hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q)
      (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d = 0 := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  have hlim := tendsto_hillEnergyProductFixedPeriod_escaping (B.shift:ℂ) (P.sourcePsi q) hreal
    (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) n hn _ d hd
  have hz : Tendsto (fun j => hillEnergyProductFixedPeriod (n j) (B.shift:ℂ) (P.sourcePsi q)
      (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_fixed_pnat_ne_escaping n hn m] with j hj
    exact (P.parent.product_off_diagonal_period_zero (n j) m hj q (P.subset hq) hr
      (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ))).symm
  exact tendsto_nhds_unique hlim hz

theorem exists_full_energy_gap_data_of_actual_real_escaping_limit (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T)) :
    ∃ d ∈ hillHminusEnergyGapData ⟨q,hr⟩, P.fullEnergyPeriodJacobianEntries q hq d T ∧
      ∀ m : ℕ+, hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q)
        (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d = 0 := by
  obtain ⟨d,hd,σ,hσ,hlim⟩ := exists_actual_hill_zero_sequence_convergent_subseq ⟨q,hr⟩ n
  have hnσ : Tendsto (fun j => (n (σ j):ℕ)) atTop atTop := hn.comp hσ.tendsto_atTop
  exact ⟨d,hd,P.fullEnergyPeriodJacobianEntries_of_escaping_limit q hq hr (fun j => n (σ j)) hnσ d hlim T
    (hT.comp hσ.tendsto_atTop),fun m => P.fullEnergyPeriod_zero_of_escaping_actual_data q hq hr
      (fun j => n (σ j)) hnσ d hlim m⟩


theorem exists_actual_real_joint_escaping_limit (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop) :
    ∃ T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      ∃ d ∈ hillHminusEnergyGapData ⟨q,hr⟩, ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => P.sequenceJacobian (n (σ j)) (hillHminusPsiZeroDisplacement (n (σ j)) ⟨q,hr⟩,q)) atTop (𝓝 T) ∧
        Tendsto (fun j => hillHminusPsiZeroDisplacement (n (σ j)) ⟨q,hr⟩) atTop (𝓝 d) ∧
        P.fullEnergyPeriodJacobianEntries q hq d T ∧
        ∀ m : ℕ+, hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q)
          (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) d = 0 := by
  obtain ⟨T,σ,hσ,hT⟩ := P.exists_actual_real_sequenceJacobian_norm_convergent_subseq q hq hr n
  obtain ⟨d,hd,τ,hτ,hdlim⟩ := exists_actual_hill_zero_sequence_convergent_subseq ⟨q,hr⟩ (fun j => n (σ j))
  have hmono : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hn' : Tendsto (fun j => (n (σ (τ j)):ℕ)) atTop atTop := hn.comp hmono.tendsto_atTop
  have hT' := hT.comp hτ.tendsto_atTop
  exact ⟨T,d,hd,σ ∘ τ,hmono,hT',hdlim,
    P.fullEnergyPeriodJacobianEntries_of_escaping_limit q hq hr (fun j => n (σ (τ j))) hn' d hdlim T hT',
    fun m => P.fullEnergyPeriod_zero_of_escaping_actual_data q hq hr (fun j => n (σ (τ j))) hn' d hdlim m⟩

end NLS.KdV.HillProductEquationPatch
