import NLS.KdV.HillQuarticEnergyContourPhase
import NLS.KdV.HillFiniteGapCubicContour

/-! At an actual finite-gap source, the Gardner bracket of the energy
contour with its canonical phase equals the exact free cubic minus12
actual second-moment series. -/
noncomputable section
open Set Metric Complex NLS.Poisson NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+} {W : Set (CoeffPair 2)}

theorem exists_finiteGap_quarticEnergyContour_phase_moment_formula
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : PeriodOneHminusOne) (hq : q ∈ A.source) (hC : q ∈ P.momentSource C)
    (hr : IsRealPeriodOneHminusOne q)
    (hf : {k : ℤ | canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) k ≠ 0}.Finite) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q) →
      hminusGardnerBracket (P.quarticEnergyContour W 0 R) A.completePhase q =
        (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n q := by
  obtain ⟨T,hT,hformula⟩ := P.exists_finiteGap_cubic_contour_moment_formula C q hC hr hf
  have hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (n:ℤ) ≠ 0 := by
    intro hz
    have hh := (A.identities q hq).1
    rw [hz,zero_pow (by norm_num : (2:ℕ)≠0),zero_div] at hh
    exact pow_ne_zero 2 (A.halfGap_ne q hq) hh
  refine ⟨T,hT,fun R hR hcircle => ?_⟩
  rw [A.quarticEnergyContour_completePhase_Gardner_of_real C 0 R (hT.trans_le hR).le q hq hC hr hcircle]
  exact hformula R hR hcircle n hn

end NLS.KdV.HillPhysicalOnIndexPhaseChart
