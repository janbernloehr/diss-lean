import NLS.KdV.HillHminusOneLogNormingDifferential

/-! # Intrinsic bounded H^-1 differentials of the actual Dirichlet data

The squared column gives the energy differential. The sine-cosine
potential pairing, corrected by its energy overlap, gives the norming
differential. Both are bounded complex-linear functionals at every real
potential, including closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def hillHminusDirichletEnergyDifferential (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : PeriodOneHminusOne →L[ℂ] ℂ := by
  let y := hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)
  have hy := hillHminusDirichletColumn_H1 q (hillHminusDirichletEnergy q hr n)
  have hend : extend y 1*extend y 1 = extend y 0*extend y 0 := by
    dsimp only [y]
    simp only [hillHminusDirichletColumn_terminal,hillHminusDirichletEnergy_zero,
      hillHminusDirichletColumn_initial,zero_mul]
  exact (1/unitIntervalMean (y*y)) • hillHminusWeakPotentialCLM y y hy.1 hy.1 hy.2 hy.2 hend

theorem hillHminusDirichletEnergyDifferential_apply (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (h : PeriodOneHminusOne) :
    hillHminusDirichletEnergyDifferential q hr n h =
      hillHminusWeakPotential h
        (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))
        (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))/
      (∫ s in (0 : ℝ)..1,
        extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s*
        extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s) := by
  simp only [hillHminusDirichletEnergyDifferential,smul_apply,smul_eq_mul,
    hillHminusWeakPotentialCLM_apply,one_div,unitIntervalMean_apply]
  rw [div_eq_mul_inv,mul_comm]
  rfl

def hillHminusDirichletNormingCosine (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : Curve ℂ :=
  (hillHminusMiuraChartAt q).physicalPosition q (hillHminusDirichletEnergy q hr n) (1,0)

def hillHminusDirichletLogNormingDifferential (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : PeriodOneHminusOne →L[ℂ] ℂ := by
  let y := hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)
  let φ := hillHminusDirichletNormingCosine q hr n
  have hy := hillHminusDirichletColumn_H1 q (hillHminusDirichletEnergy q hr n)
  have hφ := (hillHminusMiuraChartAt q).physicalSolution_scalar_H1 q (hillHminusDirichletEnergy q hr n) (1,0)
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by
    dsimp only [y]
    simp only [hillHminusDirichletColumn_terminal,hillHminusDirichletEnergy_zero,
      hillHminusDirichletColumn_initial,zero_mul]
  exact hillHminusWeakPotentialCLM y φ hy.1 hφ.1 hy.2 hφ.2.1 hend-
    unitIntervalMean (y*φ) • hillHminusDirichletEnergyDifferential q hr n

theorem hillHminusDirichletLogNormingDifferential_apply (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (h : PeriodOneHminusOne) :
    hillHminusDirichletLogNormingDifferential q hr n h =
      hillHminusWeakPotential h (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))
        (hillHminusDirichletNormingCosine q hr n)-
      (∫ s in (0 : ℝ)..1,
        extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s*
        extend (hillHminusDirichletNormingCosine q hr n) s)*hillHminusDirichletEnergyDifferential q hr n h := rfl

theorem hillHminusDirichletEnergy_branch_hasFDerivAt
    (q : PeriodOneRealHminusOne) (n : ℕ+) (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q.val)
    (haq : a q.val = (hillHminusDirichletEnergy q.val q.property n : ℂ))
    (hroot : ∀ᶠ p in 𝓝 q.val, hillHminusDirichlet p (a p) = 0) :
    HasFDerivAt a (hillHminusDirichletEnergyDifferential q.val q.property n) q.val := by
  have hz : hillHminusDirichlet q.val (a q.val) = 0 := by
    rw [haq]
    exact hillHminusDirichletEnergy_zero q.val q.property n
  have hd : fderiv ℂ a q.val = hillHminusDirichletEnergyDifferential q.val q.property n := by
    ext h
    rw [hillHminusDirichletEnergyDifferential_apply]
    simpa only [haq] using hillHminusDirichlet_branch_fderiv q.val q.property a ha hz hroot h
  rw [← hd]
  exact ha.differentiableAt.hasFDerivAt

theorem hillHminusDirichletLogNorming_extension_hasFDerivAt
    (K : PeriodOneHminusOne → ℂ) (q : PeriodOneRealHminusOne) (hK : AnalyticAt ℂ K q.val) (n : ℕ+)
    (hrec : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
      K p.val = (hillHminusDirichletLogNorming p.val p.property n : ℂ)) :
    HasFDerivAt K (hillHminusDirichletLogNormingDifferential q.val q.property n) q.val := by
  obtain ⟨a,ha,haq,hroot,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension q n
  have hDa := hillHminusDirichletEnergy_branch_hasFDerivAt q n a ha haq hroot
  have hd : fderiv ℂ K q.val = hillHminusDirichletLogNormingDifferential q.val q.property n := by
    ext h
    have hh := hillHminusDirichletLogNorming_extension_differential K q hK n hrec
      (hillHminusMiuraChartAt q.val) (mem_hillHminusMiuraChartAt q.val) a ha haq hroot hmatch h
    rw [hDa.fderiv,haq] at hh
    rw [hillHminusDirichletLogNormingDifferential_apply]
    dsimp only [hillHminusDirichletNormingCosine]
    linear_combination hh
  rw [← hd]
  exact hK.differentiableAt.hasFDerivAt

theorem hillHminusDirichletLogNormingDifferential_eq_chart
    (q : PeriodOneRealHminusOne) (n : ℕ+) (C : HillHminusMiuraChart) (hC : q.val ∈ C.domain)
    (h : PeriodOneHminusOne) :
    hillHminusDirichletLogNormingDifferential q.val q.property n h =
      hillHminusWeakPotential h
        (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n))
        (C.physicalPosition q.val (hillHminusDirichletEnergy q.val q.property n) (1,0))-
      hillHminusDirichletEnergyDifferential q.val q.property n h*
        (∫ s in (0 : ℝ)..1,
          extend (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n)) s*
          extend (C.physicalPosition q.val (hillHminusDirichletEnergy q.val q.property n) (1,0)) s) := by
  obtain ⟨K,hK,_,hrec⟩ := exists_hillHminusDirichletLogNorming_analytic_extension q n
  obtain ⟨a,ha,haq,hroot,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension q n
  have hdK := hillHminusDirichletLogNorming_extension_hasFDerivAt K q hK n hrec
  have hDa := hillHminusDirichletEnergy_branch_hasFDerivAt q n a ha haq hroot
  have hh := hillHminusDirichletLogNorming_extension_differential K q hK n hrec C hC a ha haq hroot hmatch h
  simpa only [hdK.fderiv,hDa.fderiv,haq] using hh

end NLS.KdV
