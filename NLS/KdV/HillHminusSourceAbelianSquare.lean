import NLS.KdV.HillHminusSourceEnergyGap
import NLS.KdV.HillAbelianCoordinateFactor

/-! # Exact squared physical normalization of the native source formula -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- A weighted amplitude times the normalized frequency/eta/beta factors. -/
def sourceAbelianCoordinateFormula (P : HillHminusPsiChart) (A : ℂ)
    (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  A*P.sourceNormalizedMidpoint n q*P.sourceEtaSequence q (n : ℤ)*
    Complex.exp (I*P.sourceNoncentralBeta n q)

theorem sourceAbelianCoordinateFormula_sq_eq_original (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)^2) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    (P.sourceAbelianCoordinateFormula
      ((Real.sqrt (1+(n : ℝ)) : ℂ)*hillAbelianAmplitudePrefactor q.val q.property.1 q.property.2 n)
      n (hillOriginalHminusSource q.val))^2=
      (hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ) := by
  let a := hillOriginalHminusSource q.val
  let ψ := P.dirichletSource a
  let m := canonicalPeriodicMidpoint (p := 2) (by norm_num) (by norm_num)
    (periodOnePotential ψ) (periodOnePotential_mem _) (n : ℕ)
  let g := canonicalPeriodicGap (p := 2) (by norm_num) (by norm_num)
    (periodOnePotential ψ) (periodOnePotential_mem _) (n : ℕ)
  let A := hillAbelianAmplitudePrefactor q.val q.property.1 q.property.2 n
  let b := P.sourceNoncentralBeta n a
  let e := sourceAngularEtaAnalyticPhase (p := 2) (by norm_num) (by norm_num)
    ((n : ℕ) : ℤ) P.family.roots ψ
  have ha : a∈P.sourceBetaDomain :=
    P.mem_sourceBetaDomain_of_real a hq (hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2))
  have hgap' := P.source_gap_ne_zero_of_original_halfLength_ne_zero q hq hreal houtside c hshift n hgap
  have hE : (P.sourceEtaSequence a (n : ℤ))^2=g^2*e := by
    rw [P.sourceEtaSequence_apply H a ha]
    exact H.gapWeightedEta_original_sq ψ ha.2 (n : ℕ) hgap'
  have hm : m*g=(hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ) :=
    P.source_midpoint_mul_gap_eq_original_halfLength q hq hreal houtside c hshift n
  have hphase : e*Complex.exp (2*I*b)=(hillOriginalFullPhaseFactor n q)^2 :=
    (P.originalFullPhaseFactor_sq_eq_source q hq hreal houtside c hshift H n hgap hw).symm
  have hcoord : hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n n.pos=
      (hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)*A*hillOriginalFullPhaseFactor n q := by
    rw [hillDirichletAbelianCoordinate,
      sqrt_hillAction_eq_halfLength_mul_abelianPrefactor q.val q.property.1 q.property.2 n n.pos]
    rfl
  have hsqrt : (Real.sqrt (1+(n : ℝ)) : ℂ)^2=(1+(n : ℕ) : ℂ) := by
    rw [← ofReal_pow,Real.sq_sqrt (by positivity),ofReal_add,ofReal_one,ofReal_natCast]
  have hden : (1+(n : ℕ) : ℂ)≠0 := by exact_mod_cast (show 1+(n : ℕ)≠0 by omega)
  have hexp : (Complex.exp (I*b))^2=Complex.exp (2*I*b) := by
    rw [← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  change ((Real.sqrt (1+(n : ℝ)) : ℂ)*A*(m/(1+(n : ℕ) : ℂ))*
    P.sourceEtaSequence a (n : ℤ)*Complex.exp (I*b))^2=_
  calc
    _ = (Real.sqrt (1+(n : ℝ)) : ℂ)^2*(A*(m*g))^2*
        (e*Complex.exp (2*I*b))/(1+(n : ℕ) : ℂ)^2 := by
      simp only [mul_pow,div_pow,hE,hexp]
      ring
    _ = _ := by
      rw [hsqrt,hm,hphase,hcoord]
      field_simp

end NLS.KdV.HillHminusPsiChart
