import NLS.KdV.HillOnIndexAbelianCosinePhase
import NLS.KdV.HillPhysicalOffIndexAbelianValue

/-! The actual diagonal remainder evaluated at the physical auxiliary
Dirichlet divisor. It is analytic even when its physical sheet is zero.
The associated exponential Cartesian factors use no gap division. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalOnIndexAbelianCorrection (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  P.physicalDirichletRootCoefficient n q*P.onIndexAbelianFilledRemainder n
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)

def physicalOnIndexCartesianPlus (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)-P.physicalDirichletRootCoefficient n q)*
      Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)

def physicalOnIndexCartesianMinus (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)+P.physicalDirichletRootCoefficient n q)*
      Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)

theorem analytic_physicalOnIndexAbelianCorrection (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalOnIndexAbelianCorrection n) P.physicalDirichletSource := by
  intro q hq
  have hμ := P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1
  have hH := (P.analytic_onIndexAbelianFilledRemainder n _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩).comp
    (f := fun a => (P.physicalDirichletFrequency ((n:ℕ):ℤ) a,a)) (hμ.prod analyticAt_id)
  exact (P.analytic_physicalDirichletRootCoefficient n q hq).mul hH

theorem physicalOnIndexAbelianCorrection_zero_of_sheet_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hs : hillHminusDirichletSheet n q = 0) :
    P.physicalOnIndexAbelianCorrection n q = 0 := by
  simp only [physicalOnIndexAbelianCorrection,physicalDirichletRootCoefficient,hs,zero_div,zero_mul]

theorem analytic_physicalOnIndexCartesianPlus (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalOnIndexCartesianPlus n) P.physicalDirichletSource := by
  intro q hq
  have hτ := P.analytic_abelianGapMidpoint n q hq.1
  have hμ := P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1
  have hr := P.analytic_physicalDirichletRootCoefficient n q hq
  have hc := P.analytic_physicalOnIndexAbelianCorrection n q hq
  exact ((analyticAt_const.mul hτ).mul ((hμ.sub hτ).sub hr)).mul
    (analyticAt_const.mul hc).cexp

theorem analytic_physicalOnIndexCartesianMinus (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalOnIndexCartesianMinus n) P.physicalDirichletSource := by
  intro q hq
  have hτ := P.analytic_abelianGapMidpoint n q hq.1
  have hμ := P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1
  have hr := P.analytic_physicalDirichletRootCoefficient n q hq
  have hc := P.analytic_physicalOnIndexAbelianCorrection n q hq
  exact ((analyticAt_const.mul hτ).mul ((hμ.sub hτ).add hr)).mul
    (analyticAt_const.mul hc).cexp

theorem physicalOnIndexCartesian_product (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.physicalOnIndexCartesianPlus n q*P.physicalOnIndexCartesianMinus n q =
      4*(sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))^2*
        (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2 := by
  have hs := P.physicalDirichletRootCoefficient_sq n q hq
  unfold sourceAngularSelectedPolynomial quadraticRootPolynomial at hs
  unfold physicalOnIndexCartesianPlus physicalOnIndexCartesianMinus
  have hexp : Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)*Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q) = 1 := by
    rw [← Complex.exp_add,show I*P.physicalOnIndexAbelianCorrection n q+ -I*P.physicalOnIndexAbelianCorrection n q = 0 by ring,Complex.exp_zero]
  calc
    _ = 16*(sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))^2*
      ((P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))^2-
        (P.physicalDirichletRootCoefficient n q)^2)*
        (Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)*Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)) := by ring
    _ = _ := by rw [hexp,hs]; ring

end NLS.KdV.HillProductEquationPatch
