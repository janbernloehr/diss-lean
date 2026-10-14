import NLS.ZakharovShabat.SourceDiscriminantExtension
import NLS.ZakharovShabat.SourceDiscriminantProductFormula
import NLS.ZakharovShabat.SourceDiscriminantExterior
import NLS.ZakharovShabat.SpectralProductSourceAudit

/-!
# Lemma 8.1 in the original source space, with the necessary corrections

The corrected factors have prefactors -1 and 4. Their printed rescalings
are still analytic, but cannot define the same discriminant. The trace has
an additive exterior asymptotic; the derivative retains its sine quotient.
The original zero set and multiplicities, literal products, uniqueness,
and physical Hilbert agreement are all supplied by constructed results.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The valid source assertions, with corrected product normalization and trace asymptotic. -/
structure SourceLemma8_1Data (hp : p ≠ ⊤) (hp1 : 1 < p) : Prop where
  parity_analytic : ∀ r : ℤ, r = 0 ∨ r = 1 →
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => canonicalParityProduct hp (periodOnePotential t.2) r t.1) univ
  printed_analytic :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => 2*canonicalParityProduct hp (periodOnePotential t.2) 0 t.1) univ ∧
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => canonicalParityProduct hp (periodOnePotential t.2) 1 t.1/2) univ
  discriminant_analytic :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1) univ
  compatibility : ∀ φ : CoeffPair p, ∀ z : ℂ,
    canonicalDiscriminant hp (periodOnePotential φ) z = canonicalParityProduct hp (periodOnePotential φ) 0 z+2 ∧
    canonicalDiscriminant hp (periodOnePotential φ) z = canonicalParityProduct hp (periodOnePotential φ) 1 z-2 ∧
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      canonicalParityProduct hp (periodOnePotential φ) 0 z * canonicalParityProduct hp (periodOnePotential φ) 1 z
  unique : ∀ F : ℂ × CoeffPair p → ℂ, Continuous F →
    (∀ z : ℂ, ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ), F (z,CoeffPair.ofFinsupp a) =
      classicalDiscriminant (finiteSourceCurve a) z) →
    F = fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  hilbert_extension : ∀ h2p : 2 ≤ p, ∀ φ : CoeffPair 2, ∀ z : ℂ,
    canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z =
      l2Discriminant (sourcePhysicalL2 φ) z
  hilbert_restriction : ∀ hp2 : p ≤ 2, ∀ φ : CoeffPair p, ∀ z : ℂ,
    canonicalDiscriminant hp (periodOnePotential φ) z =
      l2Discriminant (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z
  parity_products : ∀ φ : CoeffPair p, ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
    CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm (periodOnePotential φ)) N ξ η ∧
    TendstoLocallyUniformlyOn (fun M z => evenSpectralPairCutoff ξ η z M)
      (fun z => canonicalDiscriminant hp (periodOnePotential φ) z-2) atTop univ ∧
    TendstoLocallyUniformlyOn (fun M z => oddSpectralPairCutoff ξ η z M)
      (fun z => canonicalDiscriminant hp (periodOnePotential φ) z+2) atTop univ
  full_product : ∀ φ : CoeffPair p,
    TendstoLocallyUniformlyOn (fun M z => spectralPairPartialProduct
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)) z M)
      (fun z => (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4) atTop univ
  spectrum : ∀ φ : CoeffPair p, ∀ z : ℂ,
    ((canonicalDiscriminant hp (periodOnePotential φ) z)^2 = 4 ↔ z ∈ periodicSpectrum hp (periodOnePotential φ)) ∧
    analyticOrderAt (fun w => (canonicalDiscriminant hp (periodOnePotential φ) w)^2-4) z =
      (periodicAlgebraicMultiplicity hp (periodOnePotential φ) z : ℕ∞)
  exterior : ∀ φ : CoeffPair p, ∀ ε : ℝ, 0 < ε →
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
        (∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) →
        ‖canonicalDiscriminant hp (periodOnePotential ψ) z-2*cos z‖ ≤ ε*Real.exp |z.im| ∧
        ‖deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z+2*sin z‖ ≤ ε*Real.exp |z.im| ∧
        ‖deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/(-2*sin z)-1‖ ≤ ε

/-- Every finite p>1 supplies all corrected assertions of Lemma 8.1 on its original source. -/
theorem sourceLemma8_1 (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceLemma8_1Data hp hp1 where
  parity_analytic := analyticOnNhd_canonicalParityProduct_periodOne hp hp1
  printed_analytic := ⟨fun t ht => analyticAt_const.mul
    (analyticOnNhd_canonicalParityProduct_periodOne hp hp1 0 (Or.inl rfl) t ht),
    fun t ht => (analyticOnNhd_canonicalParityProduct_periodOne hp hp1 1 (Or.inr rfl) t ht).div
      analyticAt_const (by norm_num)⟩
  discriminant_analytic := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  compatibility := fun φ z => ⟨rfl,
    canonicalDiscriminant_eq_odd_sub_two_finite hp hp1 _ (periodOnePotential_mem φ) z,
    (canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 _ (periodOnePotential_mem φ) z).symm.trans
      (canonicalParityProducts_mul hp hp1 _ (periodOnePotential_mem φ) z).symm⟩
  unique := sourceDiscriminant_unique_joint_continuous hp hp1
  hilbert_extension := sourceDiscriminant_eq_l2_of_two_le hp
  hilbert_restriction := sourceDiscriminant_eq_l2_of_le_two hp
  parity_products := exists_sourceDiscriminant_parity_products hp hp1
  full_product := sourceDiscriminant_ordered_product hp hp1
  spectrum := fun φ z => ⟨canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem φ) z,
    analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem φ) z⟩
  exterior := fun φ _ hε => exists_uniform_sourceDiscriminant_exterior hp hp1 φ hε

/-- The printed prefactors cannot define a common discriminant, already at zero potential. -/
theorem sourceLemma8_1_printed_products_incompatible :
    ¬∃ Δ : ℂ, Tendsto (printedFreePeriodicProduct 0) atTop (𝓝 (Δ-2)) ∧
      Tendsto (printedFreeAntiperiodicProduct 0) atTop (𝓝 (Δ+2)) :=
  not_exists_discriminant_value_for_printed_products

/-- The literal exterior cosine quotient fails for the actual discriminant at every source. -/
theorem sourceLemma8_1_printed_cosine_quotient_false (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ¬ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ k : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*k‖) →
      ‖canonicalDiscriminant hp (periodOnePotential φ) z/(2*cos z)-1‖ ≤ (1 : ℝ)/2 :=
  not_exists_exterior_cosine_quotient_bound _

end NLS.ZakharovShabat
