import NLS.ZakharovShabat.SingleSpectralProductRatioExterior
import NLS.ZakharovShabat.CanonicalCriticalPoints
import NLS.ZakharovShabat.SourcePsiCandidate

/-! # Exterior decay of the actual psi/critical-derivative quotient

The complete canonical critical product is exactly the discriminant
derivative. The ratio of two free-normalized products and the restored
deleted root give inverse-radius decay on the separated exterior.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_threshold_sourcePsiCandidate_criticalQuotient_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z ≠ 0 ∧
      ‖sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z‖ ≤
        8/‖z‖ := by
  let β := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four hp
    (displacedRoots a) β (memℓp_displacedRoots a)
    (canonicalCriticalPoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.2 hr hrπ
  refine ⟨max R (max 1 (2*‖displacedRoots a n‖)),by positivity,?_⟩
  intro z hz hsep
  let J := jointSingleSpectralProduct (z,a)
  let D := deriv (canonicalDiscriminant hp (periodOnePotential φ)) z
  obtain ⟨hD,hbound⟩ := hR z ((le_max_left _ _).trans hz) hsep
  rw [← discriminant_derivative_eq_canonicalCriticalProduct hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ)] at hD hbound
  change D ≠ 0 at hD
  change ‖J/D‖ ≤ 4 at hbound
  have hznorm : 0 < ‖z‖ := by
    have h := (le_max_left (1:ℝ) (2*‖displacedRoots a n‖)).trans ((le_max_right R _).trans hz)
    linarith
  have hrootbound : 2*‖displacedRoots a n‖ ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right R _).trans hz)
  have hdist : ‖z‖/2 ≤ ‖z-displacedRoots a n‖ := by
    have htri := norm_add_le (z-displacedRoots a n) (displacedRoots a n)
    rw [sub_add_cancel] at htri
    linarith
  have hdistpos : 0 < ‖z-displacedRoots a n‖ := (half_pos hznorm).trans_le hdist
  have hne : z-displacedRoots a n ≠ 0 := norm_pos_iff.mp hdistpos
  have hJ : J = (z-displacedRoots a n)*sourcePsiCandidate n (z,a) := by
    dsimp only [J]
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 n]
    dsimp only [sourcePsiCandidate]
    ring
  have hψ : sourcePsiCandidate n (z,a)/D = (J/D)/(z-displacedRoots a n) := by
    rw [hJ]
    field_simp [hne]
  refine ⟨hD,?_⟩
  change ‖sourcePsiCandidate n (z,a)/D‖ ≤ 8/‖z‖
  rw [hψ,norm_div]
  apply (div_le_div_iff₀ hdistpos hznorm).mpr
  nlinarith

theorem eventually_centralCircle_sourcePsiCandidate_criticalQuotient_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z ≠ 0 ∧
      ‖sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z‖ ≤
        8/centralCircleRadius k := by
  obtain ⟨R,_,hR⟩ := exists_threshold_sourcePsiCandidate_criticalQuotient_le hp hp1 n a φ
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK)
  have hkreal : (K:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by unfold centralCircleRadius; nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hsep (m : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    have h := centralCircle_lattice_gap k hz m
    nlinarith [Real.pi_pos]
  simpa only [hnorm] using hR z (by rw [hnorm]; exact hRk) hsep

theorem eventually_sourcePsiCritical_outerCauchy_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (L : ℝ) (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ w : ℂ, ‖w‖ ≤ L →
      ‖∮ z in C(0,centralCircleRadius k),
        sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z/(z-w)‖ < ε := by
  obtain ⟨K₀,hK₀⟩ := eventually_centralCircle_sourcePsiCandidate_criticalQuotient_le hp hp1 n a φ
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt ((2*L+32*Real.pi/ε+1)/Real.pi)
  refine ⟨max K₀ K₁,?_⟩
  intro k hk w hw
  let R := centralCircleRadius k
  have hK₁ : 2*L+32*Real.pi/ε+1 < (K₁:ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₁)
  have hk₁ : (K₁:ℝ) ≤ (k:ℝ) := by exact_mod_cast ((le_max_right K₀ K₁).trans hk)
  have hlarge : 2*L+32*Real.pi/ε+1 < R := by dsimp only [R,centralCircleRadius]; nlinarith [Real.pi_pos]
  have hR : 0 < R := by have := div_pos (by positivity : 0 < 32*Real.pi) hε; linarith
  have h2L : 2*L < R := by have := div_pos (by positivity : 0 < 32*Real.pi) hε; linarith
  have hpoint (z : ℂ) (hz : z ∈ sphere (0:ℂ) R) :
      ‖sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z/(z-w)‖ ≤
        16/R^2 := by
    have hbound := (hK₀ k ((le_max_left _ _).trans hk) z hz).2
    change ‖sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z‖ ≤ 8/R at hbound
    have hzNorm : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have htri := norm_add_le (z-w) w
    rw [sub_add_cancel,hzNorm] at htri
    have hdist : R/2 ≤ ‖z-w‖ := by linarith
    rw [norm_div]
    calc
      _ ≤ (8/R)/(R/2) := (div_le_div_of_nonneg_right hbound (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity : 0 ≤ 8/R) (half_pos hR) hdist)
      _ = 16/R^2 := by field_simp; ring
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hpoint
  have hbound : 2*Real.pi*R*(16/R^2) = 32*Real.pi/R := by field_simp; ring
  rw [hbound] at hint
  apply hint.trans_lt
  apply (div_lt_iff₀ hR).mpr
  have hεR : 32*Real.pi/ε < R := by linarith
  have h := (div_lt_iff₀ hε).mp hεR
  nlinarith

end NLS.ZakharovShabat
