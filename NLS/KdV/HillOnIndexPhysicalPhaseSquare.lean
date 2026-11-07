import NLS.KdV.HillOnIndexPhysicalPhaseExponential

/-! A local analytic on-index phase modulo pi on the ACTUAL open-gap
domain. The quotient of the two physical Cartesian factors is the
exact doubled phase exponential on every physical cosine chart. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalOnIndexPhaseSquare (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ := P.physicalOnIndexCartesianPlus n q/P.physicalOnIndexCartesianMinus n q

theorem physicalOnIndexCartesian_ne_zero_of_original_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    P.physicalOnIndexCartesianPlus n q ≠ 0 ∧ P.physicalOnIndexCartesianMinus n q ≠ 0 :=
  mul_ne_zero_iff.mp ((P.physicalOnIndexCartesian_product_eq_original_gap_square n q hq).symm ▸ hgap)

theorem analytic_physicalOnIndexPhaseSquare (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalOnIndexPhaseSquare n)
      {q | q ∈ P.physicalDirichletSource ∧ hillHminusCanonicalGapSquare n q ≠ 0} := by
  intro q hq
  exact (P.analytic_physicalOnIndexCartesianPlus n q hq.1).div
    (P.analytic_physicalOnIndexCartesianMinus n q hq.1) (P.physicalOnIndexCartesian_ne_zero_of_original_gap n q hq.1 hq.2).2

theorem physicalOnIndexPhaseSquare_ne_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    P.physicalOnIndexPhaseSquare n q ≠ 0 := by
  have h := P.physicalOnIndexCartesian_ne_zero_of_original_gap n q hq hgap
  exact div_ne_zero h.1 h.2

theorem isOpen_physicalOnIndexPhaseDomain (P : HillProductEquationPatch) (n : ℕ+) :
    IsOpen {q | q ∈ P.physicalDirichletSource ∧ hillHminusCanonicalGapSquare n q ≠ 0} := by
  have hG : AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) P.physicalDirichletSource :=
    (analyticOnNhd_hillHminusCanonicalGapSquare n).mono (fun q hq => mem_iUnion.mpr
      ⟨P.parent.parent.miuraBall,(P.parent.subset (P.subset hq.1)).1⟩)
  exact hG.continuousOn.isOpen_inter_preimage P.physicalDirichletSource_open (isOpen_ne (x := (0:ℂ)))

theorem frequency_half_gap_square_ne_zero_of_original_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ≠ 0 := by
  intro hzero
  have hg : (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2 = 0 := by
    linear_combination (4:ℂ)*hzero
  have he := (P.physicalOnIndexCartesian_product_eq_original_gap_square n q hq).symm.trans
    (P.physicalOnIndexCartesian_product n q hq)
  apply hgap
  rw [he,hg,mul_zero]

theorem physicalOnIndexPhaseSquare_eq_exp_on_cover (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hgap : hillHminusCanonicalGapSquare n q ≠ 0)
    (δ θ : ℂ)
    (hpoint : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ = P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hroot : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q) :
    P.physicalOnIndexPhaseSquare n q = Complex.exp (2*I*P.onIndexAbelianCosinePhase n q δ θ) := by
  have hplus := P.physicalOnIndexCartesianPlus_eq_gap_mul_phase_exp n q δ θ hpoint hroot
  have hminus := P.physicalOnIndexCartesianMinus_eq_gap_mul_phase_exp n q δ θ hpoint hroot
  have hc : 4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*δ ≠ 0 := by
    intro he
    rw [he,zero_mul] at hplus
    exact (P.physicalOnIndexCartesian_ne_zero_of_original_gap n q hq hgap).1 hplus
  rw [physicalOnIndexPhaseSquare,hplus,hminus,mul_div_mul_left _ _ hc,← Complex.exp_sub]
  congr 1
  ring

end NLS.KdV.HillProductEquationPatch
