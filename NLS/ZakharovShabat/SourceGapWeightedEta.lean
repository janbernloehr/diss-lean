import NLS.ZakharovShabat.SourceAngularEtaRemainderGlobal
import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase

/-! # Gap-weighted eta coordinates through collapsed gaps

Section 15's two coordinates are expressed without a half-gap division.
The terminal sine numerator is the actual anti-discriminant divided by
twice the omitted root product. Together with the normalized remainder
it gives analytic formulas for both signs, including at closed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The quantity `δ sin ε`, defined without dividing by the half-gap. -/
def sourceDirichletEtaSineNumerator (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ :=
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  sourceAntiDiscriminantCandidate hp hp1 ψ μ /
    (2 * sourceStandardRootOmittedProduct hp hp1 n ψ μ)

/-- Sign `1` gives `z⁺`; sign `-1` gives `z⁻`. The formula itself
is defined at collapsed gaps, without choosing an angle there. -/
def sourceGapWeightedEtaCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (σ : ℂ) (ψ : CoeffPair p) : ℂ :=
  -2 * (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n -
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
      σ * I * sourceDirichletEtaSineNumerator hp hp1 n ψ) *
    Complex.exp (σ * I * sourceAngularEtaRemainder hp hp1 n s ψ)

/-- The terminal circle identity remains valid when the gap is zero. -/
theorem sourceDirichletEtaSineNumerator_sq_add
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceDirichletEtaSineNumerator hp hp1 n ψ ^ 2 +
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ μ
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ n hμ
  have hid : w^2 = (γ^2 - 4*(μ-τ)^2)*P^2 := by
    dsimp only [w]
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ n,
      canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) n,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ n μ hμ]
    dsimp only [γ,τ,canonicalPeriodicGap,canonicalPeriodicMidpoint,P]
    ring
  change (w/(2*P))^2 + (μ-τ)^2 = γ^2/4
  field_simp
  linear_combination 4*hid

/-- The two gap-weighted coordinates have product equal to the squared
periodic gap, including at complex collapsed gaps. -/
theorem sourceGapWeightedEtaCoordinate_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ * sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 := by
  let a := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n -
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := sourceDirichletEtaSineNumerator hp hp1 n ψ
  let H := sourceAngularEtaRemainder hp hp1 n s ψ
  have hprod : (a+I*b)*(a-I*b) = a^2+b^2 := by
    calc
      _ = a^2-I^2*b^2 := by ring
      _ = _ := by rw [I_sq]; ring
  have he : Complex.exp (I*H)*Complex.exp (-(I*H)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hs := sourceDirichletEtaSineNumerator_sq_add hp hp1 n ψ hμ
  change b^2+a^2 = _ at hs
  calc
    _ = 4*((a+I*b)*(a-I*b))*(Complex.exp (I*H)*Complex.exp (-(I*H))) := by
      simp only [sourceGapWeightedEtaCoordinate, one_mul, neg_mul]
      dsimp only [a,b,H]
      ring
    _ = _ := by rw [hprod, he]; linear_combination 4*hs

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

theorem analyticOnNhd_dirichletEtaSineNumerator
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V) :
    AnalyticOnNhd ℂ (sourceDirichletEtaSineNumerator hp hp1 n) V := by
  intro ψ hψ
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  have hμball : μ ∈ ball (c n) (T n) := (D.disc_family ψ hψ).dirichlet_mem_ball n
  have hμdom := ((D.disc_family ψ hψ).contour_family.2 n).2.2.1 (ball_subset_closedBall hμball)
  have hP := (D.omitted_analytic (μ,ψ) ⟨hμball,hψ⟩).comp
    (f := fun χ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n,χ))
    ((hμ ψ hψ).prod analyticAt_id)
  have hw := (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (μ,ψ) (mem_univ _)).comp
    (f := fun χ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n,χ))
    ((hμ ψ hψ).prod analyticAt_id)
  exact hw.div (analyticAt_const.mul hP)
    (mul_ne_zero (by norm_num) (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ n hμdom))

/-- The formula is analytic on the whole chart, not just its open-gap part. -/
theorem analyticOnNhd_gapWeightedEtaCoordinate
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V)
    (hτ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) V) (σ : ℂ) :
    AnalyticOnNhd ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) V := by
  intro ψ hψ
  exact (analyticAt_const.mul (((hμ ψ hψ).sub (hτ ψ hψ)).add
    (analyticAt_const.mul (D.analyticOnNhd_dirichletEtaSineNumerator hμ ψ hψ)))).mul
      ((analyticAt_const.mul (D.analyticOnNhd_etaRemainder ρ hrρ hρR hμ ψ hψ)).cexp')

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
