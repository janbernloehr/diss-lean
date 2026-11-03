import NLS.Articles.KdVPseudomeasures.OriginalAnalyticDirichletCoordinates
import NLS.KdV.HminusOneDirichletSheet

/-! Actual Dirichlet norming multipliers and monodromy divisor sheets on
one common complex neighborhood of the ENTIRE original real mean-zero
H-minus-one space. All Miura lifts and physical energy shifts give the
same sheet. Normalized differentials, angles and Birkhoff coordinates
remain further essential constructions. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.MKdV NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

/-- The normalized scalar Dirichlet terminal multiplier of the original potential. -/
def originalDirichletNorming (q : OriginalHminusOnePotential) (n : ℕ+) : ℂ :=
  hillHminusDirichletNorming n (originalPeriodOneCoefficients q)

/-- The original Dirichlet energy and its actual monodromy sheet. -/
def originalDirichletDivisor (q : OriginalHminusOnePotential) (n : ℕ+) : ℂ × ℂ :=
  ((originalDirichletLabels q n : ℂ),hillHminusDirichletSheet n (originalPeriodOneCoefficients q))

theorem originalDirichletNorming_ne_zero (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalDirichletNorming q n ≠ 0 :=
  hillHminusDirichletNorming_ne_zero n _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

/-- The divisor lies on the actual spectral curve, with the original discriminant. -/
theorem originalDirichletDivisor_spectral_curve (q : OriginalHminusOnePotential) (n : ℕ+) :
    (originalDirichletDivisor q n).2^2 =
      (originalHillDiscriminant q (originalDirichletDivisor q n).1)^2-4 := by
  have h := hillHminusDirichletSheet_sq n (originalPeriodOneCoefficients q)
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))
  rw [originalCanonicalDirichlet_eq q n] at h
  exact h

/-- The multiplier has the exact physical normalization for every complex L2 lift. -/
theorem originalDirichletNorming_eq_shifted_miura (q : OriginalHminusOnePotential) (n : ℕ+)
    (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = originalPeriodOneCoefficients q+periodOneL2Inclusion (lp.single 2 0 c)) :
    originalDirichletNorming q n =
      quasiHillL2DirichletTerminal u ((originalDirichletLabels q n : ℂ)+c) := by
  have h := hillHminusDirichletNorming_eq_shifted_miura n (originalPeriodOneCoefficients q)
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q)) u c hi
  rw [originalCanonicalDirichlet_eq q n] at h
  exact h

/-- The sheet's sign is the actual diagonal difference for every valid shifted lift. -/
theorem originalDirichletDivisor_eq_shifted_miura (q : OriginalHminusOnePotential) (n : ℕ+)
    (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = originalPeriodOneCoefficients q+periodOneL2Inclusion (lp.single 2 0 c)) :
    (originalDirichletDivisor q n).2 =
      quasiHillL2DirichletSheet u ((originalDirichletLabels q n : ℂ)+c) := by
  have h := hillHminusDirichletSheet_eq_shifted_miura n (originalPeriodOneCoefficients q)
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q)) u c hi
  rw [originalCanonicalDirichlet_eq q n] at h
  exact h

/-- ALL divisor components and preceding action data coexist on ONE complex domain. -/
theorem exists_originalKdV_common_analytic_Dirichlet_divisors :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) W ∧
        AnalyticOnNhd ℂ (hillHminusDirichletNorming n) W ∧
        AnalyticOnNhd ℂ (hillHminusDirichletSheet n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalActionQuotient n) W ∧
        ∀ a ∈ W, hillHminusDirichletNorming n a ≠ 0 ∧
          hillHminusDirichlet a (hillHminusCanonicalDirichlet n a) = 0 ∧
          deriv (hillHminusDirichlet a) (hillHminusCanonicalDirichlet n a) ≠ 0 ∧
          (hillHminusDirichletSheet n a)^2 =
            (hillHminusDiscriminant a (hillHminusCanonicalDirichlet n a))^2-4 := by
  refine ⟨hillHminusCanonicalDirichletDomain,isOpen_hillHminusCanonicalDirichletDomain,
    isConnected_hillHminusCanonicalDirichletDomain,
    (fun q => real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q)),?_⟩
  intro n
  refine ⟨analyticOnNhd_hillHminusCanonicalDirichlet n,
    analyticOnNhd_hillHminusDirichletNorming n,analyticOnNhd_hillHminusDirichletSheet n,
    (analyticOnNhd_hillHminusCanonicalAction_on_ratioDomain n).mono hillHminusCanonicalDirichletDomain_subset,
    (analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain n).mono hillHminusCanonicalDirichletDomain_subset,
    (analyticOnNhd_hillHminusCanonicalActionQuotient n).mono hillHminusCanonicalDirichletDomain_subset,?_⟩
  intro a ha
  exact ⟨hillHminusDirichletNorming_ne_zero n a ha,hillHminusCanonicalDirichlet_is_root n a ha,
    deriv_hillHminusCanonicalDirichlet_ne_zero n a ha,hillHminusDirichletSheet_sq n a ha⟩

end NLS.Articles.KdVPseudomeasures
