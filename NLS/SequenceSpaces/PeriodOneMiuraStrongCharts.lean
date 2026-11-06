import NLS.SequenceSpaces.PeriodOneMiuraStrongBranch
import NLS.SequenceSpaces.PeriodOneRealMiuraCharts

/-! # One actual rough Miura chart with every stronger analytic restriction

The mass and complex rough chart are chosen at an arbitrary real base
BEFORE all Sobolev orders. A concrete Neumann estimate verifies the
Jacobian on the whole rough domain. Every eligible native Sobolev source
then has a genuinely complex analytic stronger restriction of the SAME
rough branch, with exact coefficient agreement.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- ONE actual real-preserving complex rough chart works before ALL
Sobolev orders and sources. Each stronger analytic germ retains the SAME
rough branch rather than independently choosing another lift. -/
theorem exists_real_periodOneMiura_chart_all_strong_restrictions
    (q0 : PeriodOneHminusOne) (hreal0 : periodOneHminusConjugation q0=q0) (Mmin : ℕ) :
    ∃ m : ℕ, ∃ U : Set PeriodOneHminusOne, ∃ G : PeriodOneHminusOne → Coeff 2,
      Mmin≤m ∧ IsOpen U ∧ q0∈U ∧ AnalyticOnNhd ℂ G U ∧
      (∀ p∈U, periodOneShiftedMiura m (G p)=p) ∧
      (∀ p∈U, periodOneHminusConjugation p=p → periodOneL2Conjugation (G p)=G p) ∧
      (∀ p∈U, Function.Bijective (periodOneMiuraJacobian m (G p))) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈U →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈U ∧
              WeightedCoeff.sobolevToL2 ht (g p)=G (periodOneSobolevImageInclusion t ht p) ∧
              periodOneSobolevShiftedMiura m t ht (g p)=p := by
  let R : ℝ := 4*‖q0‖+1
  have hR : 0<R := by dsimp only [R];positivity
  obtain ⟨M0,hM0⟩ := exists_real_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q0)
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M1,hM1⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/8)))
  let m := max Mmin (max M0 M1)
  have hm0 : M0≤m := (le_max_left _ _).trans (le_max_right _ _)
  have hm1 : M1≤m := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨v,hv,_hvsolve,_hvreal,U0,hU0,hq0,G,hGa,hGq,hsolve,hGreal⟩ :=
    hM0 m hm0 q0 le_rfl hreal0
  let U : Set PeriodOneHminusOne := U0 ∩ G ⁻¹' ball (0 : Coeff 2) (2*R)
  have hU : IsOpen U := hGa.continuousOn.isOpen_inter_preimage hU0 isOpen_ball
  have hqU : q0∈U := by
    refine ⟨hq0,?_⟩
    change G q0∈ball (0 : Coeff 2) (2*R)
    rw [hGq,mem_ball_zero_iff]
    change ‖v‖<2*R
    change ‖v‖≤3*R/4 at hv
    linarith
  have hGaU := hGa.mono (inter_subset_left : U⊆U0)
  have hsolveU (p : PeriodOneHminusOne) (hp : p∈U) : periodOneShiftedMiura m (G p)=p :=
    hsolve p hp.1
  have hbij (p : PeriodOneHminusOne) (hp : p∈U) :
      Function.Bijective (periodOneMiuraJacobian m (G p)) := by
    apply bijective_periodOneMiuraJacobian_of_small m (G p)
    have hnorm : ‖G p‖<2*R := by simpa only [mem_preimage,mem_ball_zero_iff] using hp.2
    have hk := hM1 m hm1
    have hh := mul_le_mul_of_nonneg_left hnorm.le
      (show 0≤2*‖periodOneMassKernel m‖ by positivity)
    nlinarith
  refine ⟨m,U,G,le_max_left _ _,hU,hqU,hGaU,hsolveU,(fun p hp => hGreal p hp.1),hbij,?_⟩
  intro t ht q hq
  exact exists_analytic_strong_periodOneMiura_branch m t ht U hU G hGaU hsolveU q hq (hbij _ hq)

end NLS
