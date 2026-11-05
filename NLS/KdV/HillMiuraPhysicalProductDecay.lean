import NLS.KdV.HillMiuraNumeratorExterior
import NLS.KdV.HillMixedGapProductDecay
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.HillComplexEntirePeriodInterpolation
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillHminusOneMiuraCriticalResidues

/-! # Actual Miura numerators decay relative to physical Hill gap products

The canonical critical product is the negative physical discriminant
energy derivative. Comparing it with any physical gap-box product
transfers the actual shifted Miura quotient estimate to that product.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The full critical product is literally a full physical gap-box product. -/
theorem hillEnergyCriticalProduct_eq_gap_product (E : ℂ) :
    hillEnergyCriticalProduct q hq hr E =
      hillAbelianNumeratorProduct (fun j => hillGapCriticalPoint q hq hr (j+1)) 0 E := by
  unfold hillEnergyCriticalProduct hillAbelianNumeratorProduct
  apply tprod_congr
  intro j
  simp only [hillEnergyCriticalFactor,hillAbelianNumeratorFactor,
    if_neg (by omega : j+1 ≠ 0),hillGapRootEnergyFactor]

/-- The physical energy derivative divided by any full physical gap-box
product is bounded on all sufficiently large complete energy circles. -/
theorem exists_hillDiscriminant_derivative_gap_product_bound
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      hillAbelianNumeratorProduct roots 0 E ≠ 0 ∧
      ‖deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) E/
        hillAbelianNumeratorProduct roots 0 E‖ ≤ 4 := by
  have hc : (fun j => hillGapCriticalPoint q hq hr (j+1)) ∈ hillGapRootBox q hq hr := by
    intro j
    exact (hillGapCriticalPoint_spec q hq hr (j+1) (by omega)).1
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_mixed_ratio_bound q hq hr q hq hr
    (fun j => hillGapCriticalPoint q hq hr (j+1)) roots hc hroots
  refine ⟨K,?_⟩
  intro k hk E hE
  refine ⟨(hK k hk E hE).1,?_⟩
  rw [hillL2Discriminant_derivative_eq_energyCriticalProduct,
    hillEnergyCriticalProduct_eq_gap_product,neg_div,norm_neg]
  exact (hK k hk E hE).2

/-- This actual physical pullback supplies the exterior-decay hypothesis
in the proved entire physical period uniqueness theorem. The coefficient
identity only records the literal period-one/period-two insertion. -/
theorem eventually_hillHminusMiuraEnergyPsi_div_physical_gap_product_le
    (C : HillHminusMiuraChart) (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (n : ℤ) (u : Coeff 2)
    (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (hC : periodOneL2Inclusion u ∈ C.domain)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillHminusMiuraEnergyPsi C s n (E,periodOneL2Inclusion u)/
        hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  obtain ⟨K₁,hK₁⟩ := exists_hillHminusMiuraEnergyPsi_critical_quotient_bound C s n
    (periodOneL2Inclusion u) hC
  obtain ⟨K₂,hK₂⟩ := exists_hillDiscriminant_derivative_gap_product_bound q hq hr roots hroots
  have htrace : hillHminusDiscriminant (periodOneL2Inclusion u) =
      hillL2Discriminant (SpectralWeight.one.toCoeff q) := by
    funext E
    rw [hillHminusDiscriminant_eq_hillL2,hcoeff]
  filter_upwards [eventually_ge_atTop K₁,eventually_ge_atTop K₂,
    tendsto_centralCircleRadius_atTop.eventually_ge_atTop (128/ε)] with k hk₁ hk₂ hkbig
  intro E hE
  obtain ⟨hD,hbound⟩ := hK₁ k hk₁ E hE
  rw [htrace] at hD hbound
  obtain ⟨hP,hprod⟩ := hK₂ k hk₂ E hE
  have he : hillHminusMiuraEnergyPsi C s n (E,periodOneL2Inclusion u)/
      hillAbelianNumeratorProduct roots 0 E =
        (hillHminusMiuraEnergyPsi C s n (E,periodOneL2Inclusion u)/
          deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) E)*
          (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) E/
            hillAbelianNumeratorProduct roots 0 E) := by field_simp [hD]
  rw [he,norm_mul]
  have hρ := centralCircleRadius_pos k
  apply (mul_le_mul hbound hprod (norm_nonneg _) (by positivity)).trans
  calc
    (32/centralCircleRadius k)*4 = 128/centralCircleRadius k := by ring
    _ ≤ ε := by
      apply (div_le_iff₀ hρ).mpr
      have ht := (div_le_iff₀ hε).mp hkbig
      nlinarith

/-- The globally selected physical numerator has the same full-product
exterior decay, with its actual nonzero own-period normalization retained. -/
theorem eventually_hillSelectedPsi_div_gap_product_le
    (n : ℕ) (hn : 1 ≤ n) (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianSelectedGlobalPsi q hq hr n hn E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  let a := hillAbelianSelectedGlobalRoots q hq hr n hn
  let P := hillAbelianCandidatePeriod q hq hr a.val n n
  have hP : P ≠ 0 := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  have hPpos : 0 < ‖P‖ := norm_pos_iff.mpr hP
  filter_upwards [eventually_hillAbelianPsiCandidate_div_mixed_full_product_le q hq hr q hq hr
    a.val roots a.property hroots n hn (ε*‖P‖) (mul_pos hε hPpos)] with k hk
  intro E hE
  have he : hillAbelianSelectedGlobalPsi q hq hr n hn E/hillAbelianNumeratorProduct roots 0 E =
      (hillAbelianPsiCandidate a.val n E/hillAbelianNumeratorProduct roots 0 E)/P := by
    dsimp only [hillAbelianSelectedGlobalPsi,a,P]
    ring
  rw [he,norm_div]
  exact (div_le_iff₀ hPpos).mpr (hk E hE)

/-- The actual Miura numerator matches the globally selected physical
numerator exactly when its physical intrinsic periods are normalized.
Exterior decay is proved above, rather than assumed in this criterion. -/
theorem hillHminusMiuraEnergyPsi_eq_selected_iff_periods
    (C : HillHminusMiuraChart) (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (n : ℕ) (hn : 1 ≤ n) (u : Coeff 2)
    (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (hC : periodOneL2Inclusion u ∈ C.domain) :
    (fun E => hillHminusMiuraEnergyPsi C s (n : ℤ) (E,periodOneL2Inclusion u)) =
        hillAbelianSelectedGlobalPsi q hq hr n hn ↔
      ∀ k : ℕ, 1 ≤ k → hillIntrinsicGapPeriod q hq hr k
        (fun E => hillHminusMiuraEnergyPsi C s (n : ℤ) (E,periodOneL2Inclusion u)) =
          if k = n then 1 else 0 := by
  constructor
  · intro he k hk
    rw [he]
    exact hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
  · intro hp
    let F : ℂ → ℂ := fun E => hillHminusMiuraEnergyPsi C s (n : ℤ) (E,periodOneL2Inclusion u)
    let G := hillAbelianSelectedGlobalPsi q hq hr n hn
    let N : ℂ → ℂ := fun E => F E+(-1)*G E
    have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_hillHminusMiuraEnergyPsi_spectral C s _ _
    have hG : AnalyticOnNhd ℂ G univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
    have hM : AnalyticOnNhd ℂ (fun E => (-1)*G E) univ := analyticOnNhd_const.mul hG
    have hN : AnalyticOnNhd ℂ N univ := hF.add hM
    have hzero : N = 0 := by
      apply complex_entire_eq_zero_of_hill_periods_and_product_decay q hq hr N hN
      · intro k hk
        have hPG : hillIntrinsicGapPeriod q hq hr k G = if k = n then 1 else 0 :=
          hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
        rw [hillIntrinsicGapPeriod_add q hq hr k hk _ _ hF hM,
          hillIntrinsicGapPeriod_const_mul q hq hr k G (-1),hp k hk,hPG]
        ring
      · intro roots hroots ε hε
        filter_upwards [eventually_hillHminusMiuraEnergyPsi_div_physical_gap_product_le q hq hr
          C s (n : ℤ) u hcoeff hC roots hroots (ε/2) (by positivity),
          eventually_hillSelectedPsi_div_gap_product_le q hq hr n hn roots hroots (ε/2) (by positivity)] with k hkF hkG
        intro E hE
        change ‖(F E+(-1)*G E)/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε
        rw [add_div,mul_div_assoc]
        apply (norm_add_le _ _).trans
        rw [norm_mul,norm_neg,norm_one,one_mul]
        exact (add_le_add (hkF E hE) (hkG E hE)).trans_eq (by ring)
    funext E
    have he := congrFun hzero E
    change F E+(-1)*G E = 0 at he
    change F E = G E
    linear_combination he

end NLS.KdV
