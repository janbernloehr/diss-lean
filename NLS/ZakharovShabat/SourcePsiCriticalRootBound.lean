import NLS.ZakharovShabat.SourcePsiCriticalPeriodLowerBound

/-! # Quantitative actual psi-critical root difference

The constructed comparison control supplies the period identity and its
uniform inverse bound. Product errors and the quadratic remainder are
estimated on the actual complex gap, giving the root inequality used in
the sequence bootstrap. No choice of a complex mean-value point is made.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual cancellation equation yields a linear product-error term plus
a quadratic gap remainder, with the checked normalizing-period constant two. -/
theorem SourcePsiCriticalPeriodControl.root_difference_le
    {hp : p ≠ ⊤} {hp1 : 1 < p}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {ψ : CoeffPair p} {n k : ℤ} {c : ℝ}
    (H : SourcePsiCriticalPeriodControl hp hp1 s ψ n k c)
    (g D M d : ℝ) (hg : 0 ≤ g) (hd : 0 < d)
    (hgap : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖z-sourceCriticalRoot hp hp1 ψ k‖ ≤ g)
    (herror : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-
        sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ D)
    (hprod : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ M)
    (hden : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, d ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖) :
    ‖displacedRoots (s n ψ : Coeff p) k-sourceCriticalRoot hp hp1 ψ k‖ ≤
      2*(g*D+g^2*M/d) := by
  obtain ⟨P,havoid,hzeta,hchi,hf,hA,hid,_⟩ := H
  let rho := sourceCriticalRoot hp hp1 ψ k
  let nu := sourceCriticalRoot hp hp1 ψ n
  let zeta := sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ
  let chi := sourceCriticalDeletedQuotient hp hp1 k ψ
  let f := sourcePsiCriticalNormalizer hp hp1 n k (s n ψ) ψ
  let E := fun z : ℂ => (z-rho)*(zeta z-chi z)
  let Q := fun z : ℂ => (z-rho)^2*zeta z/(nu-z)
  let J (a : ℂ → ℂ) := (2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
    a z/sourceStandardRoot hp hp1 ψ k z)
  have hE : AnalyticOnNhd ℂ E (closedBall (P.center:ℂ) P.radius) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul (hzeta.sub hchi)
  have hQ : AnalyticOnNhd ℂ Q (closedBall (P.center:ℂ) P.radius) :=
    (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).mul hzeta).div
      (analyticOnNhd_const.sub analyticOnNhd_id) havoid
  have he : ‖J E‖ ≤ g*D := P.norm_normalized_period_le_of_gap_bound E hE (g*D) (by
    intro z hz
    rw [show E z = (z-rho)*(zeta z-chi z) from rfl,norm_mul]
    exact mul_le_mul (hgap z hz) (herror z hz) (norm_nonneg _) hg)
  have hq : ‖J Q‖ ≤ g^2*M/d := P.norm_normalized_period_le_of_gap_bound Q hQ _ (by
    intro z hz
    rw [show Q z = (z-rho)^2*zeta z/(nu-z) from rfl,norm_div,norm_mul,norm_pow]
    apply (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hd (hden z hz)).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hgap z hz) 2) (hprod z hz)
        (norm_nonneg _) (sq_nonneg g)) hd.le)
  have hi : (displacedRoots (s n ψ : Coeff p) k-rho)*J f = J E+J Q := by
    have hid' : (displacedRoots (s n ψ : Coeff p) k-rho)*
        (∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z) =
      (∮ z in C((P.center:ℂ),P.radius), E z/sourceStandardRoot hp hp1 ψ k z)+
      (∮ z in C((P.center:ℂ),P.radius), Q z/sourceStandardRoot hp hp1 ψ k z) := by
      simpa only [SourcePsiCriticalComparisonIdentity,f,E,Q,rho,nu,zeta,chi,
        sourcePsiCriticalNormalizer,div_div] using hid
    dsimp only [J]
    rw [mul_left_comm,hid',mul_add]
  have hb := norm_root_difference_le_of_period_identity
    (displacedRoots (s n ψ : Coeff p) k) rho (J f) (J E) (J Q)
    (1/2) (g*D) (g^2*M/d) (by norm_num) hA he hq hi
  convert hb using 1
  ring

end NLS.ZakharovShabat
