import NLS.ZakharovShabat.SourcePsiFullProductResolventExterior
import NLS.ZakharovShabat.SingleSpectralProductRatioExterior
import NLS.ZakharovShabat.SourcePsiLimitOperatorContour
import NLS.ComplexAnalysis.SimpleZeroInterpolation

/-!
# Interpolation uniqueness for the full product variation

The full variation divided by a gap-zero product tends uniformly to
zero on large separated circles: the ratio of the two root products
is bounded, and the full root resolvent tends to zero. The gap-zero
product has only simple zeros at real data. Its filled entire quotient
therefore vanishes by maximum modulus, and the original root values
recover the zero direction.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The undeleted variation quotient is uniformly small on the large
separated exterior for every full root direction. -/
theorem exists_threshold_sourcePsiFullProductVariation_quotient_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p) (a h : Coeff p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      entireSingleSpectralProduct ρ z ≠ 0 ∧
      ‖sourcePsiFullProductVariation a h z / entireSingleSpectralProduct ρ z‖ ≤ ε := by
  obtain ⟨Rratio,hRratio⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four
    hp (displacedRoots a) ρ (memℓp_displacedRoots a) hρlp hr hrπ
  obtain ⟨Rs,hRs⟩ := exists_threshold_sourcePsiFullProductVariation_resolvent_small
    hp hp1 a h hr hrπ (by positivity : 0 < ε/4)
  refine ⟨max Rratio Rs,?_⟩
  intro z hz hsep
  let J : ℂ := jointSingleSpectralProduct (z,a)
  let G : ℂ := entireSingleSpectralProduct ρ z
  let S : ℂ := ∑' m : ℤ, h m/(displacedRoots a m-z)
  obtain ⟨hG,hratio⟩ := hRratio z ((le_max_left _ _).trans hz) hsep
  change ‖J/G‖ ≤ 4 at hratio
  have hsmall := hRs z ((le_max_right _ _).trans hz) hsep
  have hnorm : ‖sourcePsiFullProductVariation a h z/G‖ = ‖J/G‖*‖S‖ := by
    rw [hsmall.1]
    have heq : (J*S)/G = (J/G)*S := by simp only [div_eq_mul_inv]; ring
    change ‖(J*S)/G‖ = _
    rw [heq,norm_mul]
  refine ⟨hG,?_⟩
  change ‖sourcePsiFullProductVariation a h z/G‖ ≤ ε
  rw [hnorm]
  have hS : ‖S‖ ≤ ε/4 := hsmall.2
  nlinarith [norm_nonneg S]

/-- The full variation quotient decays uniformly on the expanding
half-integer-radius circles of the interpolation argument. -/
theorem eventually_centralCircle_sourcePsiFullProductVariation_quotient_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p) (a h : Coeff p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        entireSingleSpectralProduct ρ z ≠ 0 ∧
        ‖sourcePsiFullProductVariation a h z / entireSingleSpectralProduct ρ z‖ ≤ ε := by
  obtain ⟨R,hR⟩ := exists_threshold_sourcePsiFullProductVariation_quotient_small
    hp hp1 ρ hρlp a h (by positivity : 0 < Real.pi/4) le_rfl hε
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K:ℝ)*Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere,dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hRk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

/-- Sharing the complete simple zero set of a displaced root product
forces the entire full variation to vanish identically. -/
theorem sourcePsiFullProductVariation_eq_zero_of_simpleGapZeros
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p)
    (hsimple : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      deriv (entireSingleSpectralProduct ρ) z ≠ 0)
    (a h : Coeff p)
    (hcommon : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      sourcePsiFullProductVariation a h z = 0) :
    sourcePsiFullProductVariation a h = 0 := by
  have hf := analyticOnNhd_sourcePsiFullProductVariation hp hp1 a h
  have hg := analyticOnNhd_entireSingleSpectralProduct hp ρ hρlp
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_ne_zero hp ρ hρlp
  let R : ℕ → ℝ := fun j => centralCircleRadius (j+K)
  have hbase : Tendsto centralCircleRadius atTop atTop := by
    have ht : Tendsto (fun j : ℕ => (j:ℝ)*Real.pi) atTop atTop :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).congr'
        (Filter.Eventually.of_forall (fun j => by ring))
    change Tendsto (fun j : ℕ => (j:ℝ)*Real.pi+Real.pi/2) atTop atTop
    exact ht.atTop_add tendsto_const_nhds
  have hR : Tendsto R atTop atTop := hbase.comp (tendsto_add_atTop_nat K)
  have hcircle (j : ℕ) (z : ℂ) (hz : z ∈ sphere (0:ℂ) (R j)) :
      entireSingleSpectralProduct ρ z ≠ 0 := hK (j+K) (by omega) z hz
  have hdecay (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (R j),
        ‖sourcePsiFullProductVariation a h z / entireSingleSpectralProduct ρ z‖ ≤ ε := by
    obtain ⟨Kε,hKε⟩ := eventually_centralCircle_sourcePsiFullProductVariation_quotient_small
      hp hp1 ρ hρlp a h hε
    filter_upwards [eventually_ge_atTop Kε] with j hj
    intro z hz
    exact (hKε (j+K) (by omega) z hz).2
  exact NLS.ComplexAnalysis.entire_eq_zero_of_simple_zero_interpolation
    hf hg hcommon hsimple R hR hcircle hdecay

/-- Gap placement alone separates all interpolation zeros at real
type, so the full variation vanishes on the entire plane. -/
theorem sourcePsiFullProductVariation_eq_zero_of_gapZero_sequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p)
    (hρ : ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 φ m)
    (a h : Coeff p) (hzeros : ∀ m : ℤ, sourcePsiFullProductVariation a h (ρ m) = 0) :
    sourcePsiFullProductVariation a h = 0 := by
  let b : Coeff p := ⟨fun m => ρ m-(Real.pi:ℂ)*m,hρlp⟩
  have hroot (m : ℤ) : displacedRoots b m = ρ m := by dsimp [b,displacedRoots]; ring
  have hb : b ∈ sourcePeriodicGapRootSet hp hp1 φ := by
    intro m
    rw [hroot]
    exact hρ m
  have hρinj : Function.Injective ρ := by
    have hsep := displacedRoots_injective_of_periodicGapRootSet hp hp1 b φ hφ hb
    intro i j hij
    apply hsep
    rwa [hroot i,hroot j]
  apply sourcePsiFullProductVariation_eq_zero_of_simpleGapZeros hp hp1 ρ hρlp
    (entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 ρ hρlp hρinj) a h
  intro z hz
  obtain ⟨m,hm⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp ρ hρlp z).mp hz
  rw [← hm]
  exact hzeros m

/-- At gap-contained original roots, a complete gap-zero sequence
forces every coefficient of the full direction to vanish. -/
theorem sourcePsiFullProductVariation_direction_zero_of_gapZero_sequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p)
    (hρ : ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 φ m)
    (a h : Coeff p) (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (hzeros : ∀ m : ℤ, sourcePsiFullProductVariation a h (ρ m) = 0) : h = 0 := by
  have hzero := sourcePsiFullProductVariation_eq_zero_of_gapZero_sequence
    hp hp1 φ hφ ρ hρlp hρ a h hzeros
  apply sourcePsiFullProductVariation_zero_imp_direction_zero_of_gapRoots hp hp1 a h φ hφ ha
  intro z
  exact congrFun hzero z

end NLS.ZakharovShabat
