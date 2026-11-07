import NLS.KdV.HillMiuraDiscriminantSourceDerivative
import NLS.KdV.HillDiscriminantContourInvolution

/-! Genuine full source-dual integrands for the actual Hill action
after the shifted quadratic Miura energy change. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillMiuraActionCotangentIntegrand (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ) :
    PeriodOneHminusOne →L[ℂ] ℂ :=
  (z/sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal u) z) •
    hillHminusDiscriminantCotangent (z^2-c) q

theorem analyticOnNhd_hillMiuraActionCotangentIntegrand
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ) :
    AnalyticOnNhd ℂ (hillMiuraActionCotangentIntegrand q u c)
      (sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) := by
  intro z hz
  have hroot := sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) (hillMiuraDiagonal u) z hz
  have hnz := sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) (hillMiuraDiagonal u) z hz
  have hL := (analyticOnNhd_hillHminusDiscriminantCotangent_energy q (z^2-c) (mem_univ _)).comp
    (f := fun w : ℂ => w^2-c) ((analyticAt_id.pow 2).sub analyticAt_const)
  exact (analyticAt_id.div hroot hnz).smul hL

theorem circleIntegrable_hillMiuraActionCotangentIntegrand
    (q : PeriodOneHminusOne) (u : Coeff 2) (c a : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere a R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) :
    CircleIntegrable (hillMiuraActionCotangentIntegrand q u c) a R :=
  ((analyticOnNhd_hillMiuraActionCotangentIntegrand q u c).continuousOn.mono hc).circleIntegrable hR

theorem hillMiuraActionCotangentIntegrands_Gardner_commute
    (q : PeriodOneHminusOne) (u v : Coeff 2) (c d z w : ℂ) :
    NLS.Poisson.gardnerCotangentBivector (hillMiuraActionCotangentIntegrand q u c z)
      (hillMiuraActionCotangentIntegrand q v d w)=0 := by
  simp only [hillMiuraActionCotangentIntegrand,map_smul,smul_apply,
    hillHminusDiscriminantCotangents_Gardner_commute,smul_zero]

theorem hillMiuraActionCotangentContours_Gardner_commute
    (q : PeriodOneHminusOne) (u v : Coeff 2) (c d a b : ℂ) (R S : ℝ)
    (hf : CircleIntegrable (hillMiuraActionCotangentIntegrand q u c) a R)
    (hg : CircleIntegrable (hillMiuraActionCotangentIntegrand q v d) b S) :
    NLS.Poisson.gardnerCotangentBivector (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q u c z)
      (∮ w in C(b,S), hillMiuraActionCotangentIntegrand q v d w)=0 := by
  rw [NLS.ComplexAnalysis.bilinear_circleIntegral _ hf hg]
  simp only [hillMiuraActionCotangentIntegrands_Gardner_commute]
  simp [circleIntegral]

end NLS.KdV
