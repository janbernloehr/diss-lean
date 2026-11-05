import NLS.KdV.HillHminusNormingCharts
import NLS.KdV.HillCharacteristicLogSheet

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- Every original real labelled Dirichlet energy and its physical norming
multiplier/logarithm have genuine H-minus-one analytic extensions. All three
retain their original physical labels and normalizations, including collapsed
gaps. The actual trace relation holds on a full complex neighborhood. -/
theorem exists_hillDirichlet_norming_hminus_analytic_extension
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a T k : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ a (hillOriginalHminusSource q.val) ∧
      AnalyticAt ℂ T (hillOriginalHminusSource q.val) ∧
      AnalyticAt ℂ k (hillOriginalHminusSource q.val) ∧
      a (hillOriginalHminusSource q.val)=
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      T (hillOriginalHminusSource q.val)=hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) ∧
      k (hillOriginalHminusSource q.val)=
        (hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (hillOriginalHminusSource q.val),
        hillHminusDirichlet p (a p)=0 ∧ T p≠0 ∧ exp (k p)=(-1 : ℂ)^n*T p ∧
          hillHminusDiscriminant p (a p)=(T p)⁻¹+T p) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (hillOriginalHminusSource p.val)=
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        T (hillOriginalHminusSource p.val)=hillL2DirichletSlope (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn) ∧
        k (hillOriginalHminusSource p.val)=
          (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ) := by
  obtain ⟨a,ha,ha0,hroot,hmatch⟩ := exists_hillDirichletEnergy_hminus_analytic_extension q n hn
  let b := hillOriginalHminusSource q.val
  let C := hillHminusMiuraChartAt b
  have hb : b∈C.domain := mem_hillHminusMiuraChartAt b
  let T := C.dirichletTerminal a
  have hT : AnalyticAt ℂ T b := C.analyticAt_dirichletTerminal a b hb ha
  have hz : hillHminusDirichlet b (a b)=0 := hroot.self_of_nhds
  have hT0 : T b=hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) := by
    dsimp only [T,b]
    rw [C.dirichletTerminal_original_source a q.val q.property.1 hb hz,ha0]
  let M (p : PeriodOneHminusOne) := (-1 : ℂ)^n*T p
  have hM : AnalyticAt ℂ M b := analyticAt_const.mul hT
  have hM0 : M b=(hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [M]
    rw [hT0,←hillDirichletMultiplier_ofReal]
  have hslit : M b∈slitPlane := by
    rw [hM0]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  let k (p : PeriodOneHminusOne) := log (M p)
  have hk : AnalyticAt ℂ k b := hM.clog hslit
  have hk0 : k b=(hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [k]
    rw [hM0,←Complex.ofReal_log (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn).le]
    rfl
  have hC : C.domain∈𝓝 b := C.domain_open.mem_nhds hb
  refine ⟨a,T,k,ha,hT,hk,ha0,hT0,hk0,?_,?_⟩
  · have hne : ∀ᶠ p in 𝓝 b, M p≠0 :=
      hM.continuousAt.eventually_ne (slitPlane_ne_zero hslit)
    filter_upwards [hroot,hC,hne] with p hp hCp hMp
    exact ⟨hp,C.dirichletTerminal_ne_zero_of_root a p hCp hp,Complex.exp_log hMp,
      C.discriminant_eq_dirichletTerminal_inv_add a p hCp hp⟩
  · have hP : Continuous (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val) :=
      hillOriginalHminusSource.continuous.comp continuous_subtype_val
    filter_upwards [hmatch,hP.continuousAt.tendsto.eventually hroot,
      hP.continuousAt.tendsto.eventually hC] with p hp hr hCp
    have hTp : T (hillOriginalHminusSource p.val)=hillL2DirichletSlope (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn) := by
      dsimp only [T]
      rw [C.dirichletTerminal_original_source a p.val p.property.1 hCp hr,hp]
    refine ⟨hp,hTp,?_⟩
    change log (M (hillOriginalHminusSource p.val))=_
    have hMp : M (hillOriginalHminusSource p.val)=
        (hillDirichletMultiplier p.val p.property.1 p.property.2 n hn : ℂ) := by
      dsimp only [M]
      rw [hTp,←hillDirichletMultiplier_ofReal]
    rw [hMp,←Complex.ofReal_log (hillDirichletMultiplier_pos p.val p.property.1 p.property.2 n hn).le]
    rfl

end NLS.KdV
