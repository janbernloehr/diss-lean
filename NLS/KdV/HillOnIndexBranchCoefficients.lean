import NLS.KdV.HillOnIndexPhysicalPhaseSquare
import NLS.ComplexAnalysis.QuadraticPhaseEvenOdd

/-! Analytic even/odd coefficients of the ACTUAL diagonal Cartesian
factors, across the ENTIRE assigned disc and native source patch.
Their physical evaluation is A plus/minus ACTUAL Hill sheet times B. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def onIndexBranchCoordinates (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ × ℂ :=
  (sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ) t.1,
    P.onIndexAbelianFilledRemainder n t)

def onIndexFrequencyEven (P : HillProductEquationPatch) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)*
    ((t.1-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ))*rootPhaseEven (P.onIndexBranchCoordinates n t)-
      (P.onIndexBranchCoordinates n t).1*rootPhaseOdd (P.onIndexBranchCoordinates n t))

def onIndexFrequencyOdd (P : HillProductEquationPatch) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (-4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)/P.abelianGapRootMultiplier n t)*
    ((t.1-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ))*rootPhaseOdd (P.onIndexBranchCoordinates n t)-
      rootPhaseEven (P.onIndexBranchCoordinates n t))

theorem analytic_onIndexBranchCoordinates (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexBranchCoordinates n)
      (ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  have hτ := (P.analytic_abelianGapMidpoint n t.2 ht.2).comp (f := Prod.snd) analyticAt_snd
  have hgap := (P.parent.parent.miuraBall.dirac_gap_square_analytic ((n:ℕ):ℤ) t.2 (P.parent.subset (P.subset ht.2)).1).comp
    (f := Prod.snd) analyticAt_snd
  exact (((analyticAt_fst.sub hτ).pow 2).sub hgap.div_const).prod
    (P.analytic_onIndexAbelianFilledRemainder n t ht)

theorem analytic_onIndexFrequencyEven (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexFrequencyEven n)
      (ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  have hc := P.analytic_onIndexBranchCoordinates n t ht
  have hC := (analyticOnNhd_rootPhaseEven _ (mem_univ _)).comp (f := P.onIndexBranchCoordinates n) hc
  have hS := (analyticOnNhd_rootPhaseOdd _ (mem_univ _)).comp (f := P.onIndexBranchCoordinates n) hc
  have hQ := analyticAt_fst.comp (f := P.onIndexBranchCoordinates n) hc
  have hτ := (P.analytic_abelianGapMidpoint n t.2 ht.2).comp (f := Prod.snd) analyticAt_snd
  exact (analyticAt_const.mul hτ).mul (((analyticAt_fst.sub hτ).mul hC).sub (hQ.mul hS))

theorem analytic_onIndexFrequencyOdd (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexFrequencyOdd n)
      (ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  have hc := P.analytic_onIndexBranchCoordinates n t ht
  have hC := (analyticOnNhd_rootPhaseEven _ (mem_univ _)).comp (f := P.onIndexBranchCoordinates n) hc
  have hS := (analyticOnNhd_rootPhaseOdd _ (mem_univ _)).comp (f := P.onIndexBranchCoordinates n) hc
  have hτ := (P.analytic_abelianGapMidpoint n t.2 ht.2).comp (f := Prod.snd) analyticAt_snd
  exact ((analyticAt_const.mul hτ).div (P.analytic_abelianGapRootMultiplier n t ht)
    (P.abelianGapRootMultiplier_ne_zero n t ht)).mul (((analyticAt_fst.sub hτ).mul hS).sub hC)

theorem onIndexFrequencyEven_add_root_mul_odd (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) (r : ℂ)
    (hr : r^2 = (P.onIndexBranchCoordinates n t).1) :
    P.onIndexFrequencyEven n t+(P.abelianGapRootMultiplier n t*r)*P.onIndexFrequencyOdd n t =
      -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)*
        (t.1-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)-r)*
          Complex.exp (I*r*P.onIndexAbelianFilledRemainder n t) := by
  have he := rootPhase_even_add_odd r (P.onIndexAbelianFilledRemainder n t)
  rw [hr] at he
  change rootPhaseEven (P.onIndexBranchCoordinates n t)+r*rootPhaseOdd (P.onIndexBranchCoordinates n t) = _ at he
  rw [← he]
  unfold onIndexFrequencyEven onIndexFrequencyOdd
  have hK := P.abelianGapRootMultiplier_ne_zero n t ht
  field_simp [hK]
  linear_combination -(sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)*
    rootPhaseOdd (P.onIndexBranchCoordinates n t))*hr

theorem onIndexFrequencyEven_sub_root_mul_odd (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) (r : ℂ)
    (hr : r^2 = (P.onIndexBranchCoordinates n t).1) :
    P.onIndexFrequencyEven n t-(P.abelianGapRootMultiplier n t*r)*P.onIndexFrequencyOdd n t =
      -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)*
        (t.1-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)+r)*
          Complex.exp (-I*r*P.onIndexAbelianFilledRemainder n t) := by
  have he := rootPhase_even_sub_odd r (P.onIndexAbelianFilledRemainder n t)
  rw [hr] at he
  change rootPhaseEven (P.onIndexBranchCoordinates n t)-r*rootPhaseOdd (P.onIndexBranchCoordinates n t) = _ at he
  rw [← he]
  unfold onIndexFrequencyEven onIndexFrequencyOdd
  have hK := P.abelianGapRootMultiplier_ne_zero n t ht
  field_simp [hK]
  linear_combination -(sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ)*
    rootPhaseOdd (P.onIndexBranchCoordinates n t))*hr

theorem physicalOnIndexCartesian_eq_frequency_coefficients (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.physicalOnIndexCartesianPlus n q =
      P.onIndexFrequencyEven n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)+
        hillHminusDirichletSheet n q*P.onIndexFrequencyOdd n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q) ∧
    P.physicalOnIndexCartesianMinus n q =
      P.onIndexFrequencyEven n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)-
        hillHminusDirichletSheet n q*P.onIndexFrequencyOdd n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q) := by
  have ht : (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q) ∈
      ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source := ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩
  have hp := P.onIndexFrequencyEven_add_root_mul_odd n _ ht _ (P.physicalDirichletRootCoefficient_sq n q hq)
  have hm := P.onIndexFrequencyEven_sub_root_mul_odd n _ ht _ (P.physicalDirichletRootCoefficient_sq n q hq)
  rw [P.physicalDirichletRootCoefficient_preserves_sheet n q hq] at hp hm
  constructor
  · simpa only [physicalOnIndexCartesianPlus,physicalOnIndexAbelianCorrection,mul_assoc] using hp.symm
  · simpa only [physicalOnIndexCartesianMinus,physicalOnIndexAbelianCorrection,mul_assoc] using hm.symm

end NLS.KdV.HillProductEquationPatch
