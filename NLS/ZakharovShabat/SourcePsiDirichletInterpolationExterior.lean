import NLS.ZakharovShabat.SingleSpectralProductRatioExterior
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.ZakharovShabat.SourcePsiCandidate
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Exterior decay for actual Dirichlet interpolation

Restoring the omitted numerator root gives a ratio of two full products.
Their proved exterior bound supplies a uniform inverse-radius estimate
for the actual psi numerator divided by the actual Dirichlet characteristic.
The outer Cauchy integrals consequently vanish uniformly for bounded
evaluation parameters.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Dirichlet quotient has inverse-radius decay on the
large separated exterior, for every finite-exponent numerator sequence. -/
theorem exists_threshold_sourcePsiCandidate_dirichletQuotient_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi : ℂ)*m‖) →
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z ≠ 0 ∧
      ‖sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z‖ ≤ 16/‖z‖ := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ
  have hμlp : Memℓp (fun m => μ m-(Real.pi : ℂ)*m) p :=
    (sourceBoundaryDisplacement hp hp1 .dirichlet φ).property
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four hp
    (displacedRoots a) μ (memℓp_displacedRoots a) hμlp hr hrπ
  refine ⟨max R (max 1 (2*‖displacedRoots a n‖)),by positivity,?_⟩
  intro z hz hsep
  let G := entireSingleSpectralProduct μ z
  let J := jointSingleSpectralProduct (z,a)
  let D := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z
  obtain ⟨hG,hratio⟩ := hR z ((le_max_left _ _).trans hz) hsep
  change G ≠ 0 at hG
  change ‖J/G‖ ≤ 4 at hratio
  have hD : D = (-1/2 : ℂ)*G := by
    change periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z = _
    rw [periodOneBoundaryCharacteristic_eq_canonicalProduct]
    rfl
  have hDne : D ≠ 0 := by rw [hD]; exact mul_ne_zero (by norm_num) hG
  have hznorm : 0 < ‖z‖ := by
    have h := (le_max_left (1 : ℝ) (2*‖displacedRoots a n‖)).trans
      ((le_max_right R _).trans hz)
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
  have hJD : J/D = (-2 : ℂ)*(J/G) := by
    rw [hD]
    field_simp
  have hJDnorm : ‖J/D‖ ≤ 8 := by
    rw [hJD,norm_mul]
    norm_num only [norm_neg,norm_ofNat]
    linarith
  have hψ : sourcePsiCandidate n (z,a)/D = (J/D)/(z-displacedRoots a n) := by
    rw [hJ]
    field_simp [hne]
  refine ⟨hDne,?_⟩
  change ‖sourcePsiCandidate n (z,a)/D‖ ≤ 16/‖z‖
  rw [hψ,norm_div]
  apply (div_le_div_iff₀ hdistpos hznorm).mpr
  nlinarith

/-- The actual quotient's bound is uniform on all sufficiently large
half-integer-radius circles. -/
theorem eventually_centralCircle_sourcePsiCandidate_dirichletQuotient_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z ≠ 0 ∧
      ‖sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z‖ ≤
        16/centralCircleRadius k := by
  obtain ⟨R,_,hR⟩ := exists_threshold_sourcePsiCandidate_dirichletQuotient_le hp hp1 n a φ
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK)
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hsep (m : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖ := by
    have h := centralCircle_lattice_gap k hz m
    nlinarith [Real.pi_pos]
  simpa only [hnorm] using hR z (by rw [hnorm]; exact hRk) hsep

/-- The actual outer Cauchy error vanishes uniformly for every bounded
family of evaluation parameters; no interpolation identity is assumed. -/
theorem eventually_sourcePsiDirichlet_outerCauchy_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (L : ℝ) (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ w : ℂ, ‖w‖ ≤ L →
      ‖∮ z in C(0,centralCircleRadius k),
        sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z/(z-w)‖ < ε := by
  obtain ⟨K₀,hK₀⟩ := eventually_centralCircle_sourcePsiCandidate_dirichletQuotient_le hp hp1 n a φ
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt ((2*L+64*Real.pi/ε+1)/Real.pi)
  refine ⟨max K₀ K₁,?_⟩
  intro k hk w hw
  let R := centralCircleRadius k
  have hK₁ : 2*L+64*Real.pi/ε+1 < (K₁ : ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₁)
  have hk₁ : (K₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast ((le_max_right K₀ K₁).trans hk)
  have hlarge : 2*L+64*Real.pi/ε+1 < R := by
    dsimp only [R,centralCircleRadius]
    nlinarith [Real.pi_pos]
  have hR : 0 < R := by
    have h := div_pos (by positivity : 0 < 64*Real.pi) hε
    linarith
  have h2L : 2*L < R := by
    have h := div_pos (by positivity : 0 < 64*Real.pi) hε
    linarith
  have hpoint (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
      ‖sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z/(z-w)‖ ≤
        32/R^2 := by
    have hbound := (hK₀ k ((le_max_left _ _).trans hk) z hz).2
    change ‖sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z‖ ≤ 16/R at hbound
    have hzNorm : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have htri := norm_add_le (z-w) w
    rw [sub_add_cancel,hzNorm] at htri
    have hdist : R/2 ≤ ‖z-w‖ := by linarith
    rw [norm_div]
    calc
      _ ≤ (16/R)/(R/2) :=
        (div_le_div_of_nonneg_right hbound (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left (by positivity : 0 ≤ 16/R) (half_pos hR) hdist)
      _ = 32/R^2 := by field_simp; ring
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hpoint
  have hbound : 2*Real.pi*R*(32/R^2) = 64*Real.pi/R := by field_simp; ring
  rw [hbound] at hint
  apply hint.trans_lt
  apply (div_lt_iff₀ hR).mpr
  have hεR : 64*Real.pi/ε < R := by linarith
  have h := (div_lt_iff₀ hε).mp hεR
  nlinarith

end NLS.ZakharovShabat
