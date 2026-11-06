import NLS.KdV.HillHminusIntrinsicPeriods
import NLS.KdV.HillHminusNumeratorReality
import NLS.KdV.HillGlobalDifferentialUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The fixed original normalized physical numerator has the full-product
decay required by the original entire-period uniqueness theorem. -/
theorem eventually_hillSelectedPsi_div_full_product_small
    (q : RealPeriodOneHillPotential) (n : ℕ+) (roots : ℕ → ℝ)
    (hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
        hillAbelianNumeratorProduct roots 0 E‖≤ε := by
  let selected := (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n n.pos).val
  have hs : selected∈hillGapRootBox q.val q.property.1 q.property.2 :=
    (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n n.pos).property
  let C := hillAbelianCandidatePeriod q.val q.property.1 q.property.2 selected n n
  have hC : 0<‖C‖ := norm_pos_iff.mpr
    (hillAbelianCandidatePeriod_own_ne_zero q.val q.property.1 q.property.2 selected hs n n.pos)
  filter_upwards [eventually_hillAbelianPsiCandidate_div_full_product_le q.val q.property.1 q.property.2
    selected roots hs hroots n n.pos (ε*‖C‖) (mul_pos hε hC)] with k hk
  intro E hE
  change ‖(hillAbelianPsiCandidate selected n E/C)/hillAbelianNumeratorProduct roots 0 E‖≤ε
  have he (a b d : ℂ) : a/b/d=a/d/b := by ring
  rw [he,norm_div]
  exact (div_le_iff₀ hC).mpr (hk E hE)

/-- All normalization, reality and entire-period uniqueness obligations
for the FIXED original physical Hill numerator are discharged. The sole
remaining hypothesis here is the explicit full-product decay estimate. -/
theorem HillHminusPsiChart.numerator_eq_original_of_product_decay (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+)
    (hdecay : ∀ roots∈hillGapRootBox q.val q.property.1 q.property.2,
      ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((centralCircleRadius k)^2),
        ‖P.numerator n (E,hillOriginalHminusSource q.val)/hillAbelianNumeratorProduct roots 0 E‖≤ε) :
    (fun E => P.numerator n (E,hillOriginalHminusSource q.val))=
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos := by
  let N : ℂ → ℂ := fun E => P.numerator n (E,hillOriginalHminusSource q.val)
  let Q := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos
  let F : ℂ → ℂ := fun E => N E-Q E
  have hN : AnalyticOnNhd ℂ N univ := by
    intro E _
    exact (P.analytic_numerator n (E,hillOriginalHminusSource q.val) ⟨mem_univ _,hq⟩).comp
      (f := fun z : ℂ => (z,hillOriginalHminusSource q.val)) (analyticAt_id.prod analyticAt_const)
  have hQ : AnalyticOnNhd ℂ Q univ :=
    analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q.val q.property.1 q.property.2 n n.pos
  have hFre : ∀ x : ℝ, (F (x:ℂ)).im=0 := by
    intro x
    have hNr := P.numerator_real_of_real _
      (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))
      (c^2) (by simpa only [ofReal_pow] using hshift) n x
    have hc := hillAbelianSelectedGlobalPsi_conj q.val q.property.1 q.property.2 n n.pos (x:ℂ)
    rw [conj_ofReal] at hc
    have hQr := Complex.conj_eq_iff_im.mp hc.symm
    exact sub_eq_zero.mpr (hNr.trans hQr.symm)
  have hperiod (k : ℕ) (hk : 1≤k) : hillIntrinsicGapPeriod q.val q.property.1 q.property.2 k F=0 := by
    have hp := P.intrinsic_period_numerator q hq hreal houtside c hshift n ⟨k,hk⟩
    have hp' : hillIntrinsicGapPeriod q.val q.property.1 q.property.2 k N=
        (if k=(n:ℕ) then 1 else 0) := by
      split_ifs at hp with hmn
      · have hkn : k=(n:ℕ) := congrArg (fun m : ℕ+ => (m:ℕ)) hmn
        simpa [N,hkn] using hp
      · have hkn : k≠(n:ℕ) := fun h => hmn (PNat.coe_injective h)
        simpa [N,hkn] using hp
    have hqp := hillAbelianSelectedGlobalPsi_intrinsic_periods q.val q.property.1 q.property.2 n n.pos k hk
    change hillIntrinsicGapPeriod q.val q.property.1 q.property.2 k Q=_ at hqp
    have he : F=(fun E => N E+(-1:ℂ)*Q E) := by funext E; dsimp only [F]; ring
    rw [he,hillIntrinsicGapPeriod_add q.val q.property.1 q.property.2 k hk N _ hN
      (analyticOnNhd_const.mul hQ),hillIntrinsicGapPeriod_const_mul,hp',hqp]
    ring
  have hzero : F=0 := by
    apply entire_eq_zero_of_hill_periods_and_product_decay q.val q.property.1 q.property.2 F
      (hN.sub hQ) hFre hperiod
    intro roots hroots ε hε
    filter_upwards [hdecay roots hroots (ε/2) (by positivity),
      eventually_hillSelectedPsi_div_full_product_small q n roots hroots (ε/2) (by positivity)] with k hk₁ hk₂
    intro E hE
    change ‖(N E-Q E)/hillAbelianNumeratorProduct roots 0 E‖≤ε
    rw [sub_div]
    exact (norm_sub_le _ _).trans (by linarith [hk₁ E hE,hk₂ E hE])
  funext E
  exact sub_eq_zero.mp (congrFun hzero E)

end NLS.KdV
