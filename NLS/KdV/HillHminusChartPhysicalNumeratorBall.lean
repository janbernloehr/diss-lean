import NLS.KdV.HillHminusMiuraPhysicalNumerators

/-! A real-preserving actual Miura chart with positive real shift supports
original physical numerator identification on one common rough ball. The
radius is independent of the index and of the chosen verified root factory. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- The negative of any positive real shift is outside the actual rough
spectrum on a genuine complex source neighborhood of zero. -/
theorem exists_hillHminus_ball_outside_negative_shift (a : ℂ) (ha : 0<a.re) :
    ∃ δ : ℝ, 0<δ ∧ ∀ q∈ball (0 : PeriodOneHminusOne) δ, hillHminusRadicand q (-a)≠0 := by
  have hz : hillHminusRadicand 0 (-a)≠0 := by
    intro he
    have h0r : IsRealPeriodOneHminusOne 0 := by intro k; simp
    obtain ⟨j,hj⟩ := (hillHminusRealLabels_root_iff 0 h0r _).mp he
    have heq := congrArg Complex.re hj
    simp only [neg_re,ofReal_re,hillHminusRealLabels_zero,freeHillValue] at heq
    have hnonneg : 0 ≤ (((j+1)/2 : ℕ) : ℝ)^2*Real.pi^2 := by positivity
    nlinarith
  have hcont : Continuous (fun q => hillHminusRadicand q (-a)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ((analyticOnNhd_hillHminusRadicand_joint (-a,q) (mem_univ _)).comp
      (f := fun b : PeriodOneHminusOne => (-a,b)) (analyticAt_const.prod analyticAt_id)).continuousAt
  exact Metric.isOpen_iff.mp (isClosed_singleton.isOpen_compl.preimage hcont) 0 hz

/-- The SAME actual series chart and root factory have the original
physical entire numerator on one common rough ball. No physical matching
or outside-spectrum premise is assumed. -/
theorem HillHminusMiuraChart.exists_original_numerator_ball (C : HillHminusMiuraChart)
    (h0C : 0∈C.domain) (hpos : 0<C.energyShift.re) (him : C.energyShift.im=0)
    (hr : ∀ q∈C.domain, IsRealPeriodOneHminusOne q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s) :
    ∃ δ : ℝ, 0<δ ∧ ball (0 : PeriodOneHminusOne) δ⊆C.domain ∧
      ∀ q : RealPeriodOneHillPotential, hillOriginalHminusSource q.val∈ball (0 : PeriodOneHminusOne) δ →
        ∀ n : ℕ+, ∀ E : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (E,hillOriginalHminusSource q.val)=
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E := by
  obtain ⟨δ₀,hδ₀,hout⟩ := exists_hillHminus_ball_outside_negative_shift C.energyShift hpos
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp (C.domain_open.inter isOpen_ball) 0
    ⟨h0C,mem_ball_self hδ₀⟩
  have hc : C.energyShift=(Real.sqrt C.energyShift.re : ℂ)^2 := by
    rw [←ofReal_pow,Real.sq_sqrt hpos.le]
    exact Complex.ext (by simp) (by simpa using him)
  obtain ⟨B⟩ := nonempty_miuraHillPsiFamily
  let P : HillHminusPsiChart := ⟨C,B⟩
  refine ⟨δ,hδ,(fun q hq => (hsub hq).1),?_⟩
  intro q hq n E
  have hqC := (hsub hq).1
  have hqP := P.original_source_mem_of_real q hqC
    (hr _ hqC (hillOriginalHminusSource_real q.val q.property.2))
  exact P.miuraEnergyPsi_eq_original H q hqP hr (hout _ (hsub hq).2)
    (Real.sqrt C.energyShift.re) hc n E

end NLS.KdV
