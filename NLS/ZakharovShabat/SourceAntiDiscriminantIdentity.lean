import NLS.ZakharovShabat.FiniteSourceAntiDiscriminant
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.ZakharovShabat.ExponentCanonicalProducts

/-!
# The source discriminant and anti-discriminant identity

The classical unimodular monodromy identity is transferred first to finite
Fourier source data, then to the completed source spaces by density and
joint analyticity. It implies the simple Dirichlet eigenvalue identity in
Lemma 9.2(ii), and in fact needs no simplicity assumption.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Ordinary source boundary products on finite input are the literal
classical separated monodromy characteristics. -/
theorem periodOneBoundaryCharacteristic_finite_eq_classical
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) b
      (CoeffPair.ofFinsupp (p := 2) a) z =
        classicalSeparatedCharacteristic b (finiteSourceCurve a) z := by
  let Φ := finiteSourceCurve a
  have hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)) :=
    memLp_extend_classicalCurve Φ
  have hbase : BoundaryCondition.periodOnePair a =ᵐ[volume.restrict (Ioc 0 1)]
      extend Φ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (extend_finiteSourceCurve a x (Ioc_subset_Icc_self hx)).symm
  have hcoeff : (periodOneBoundaryPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val =
      intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ) := by
    rw [periodOneBoundaryPotential_finite_eq a (memLp_periodOnePair_finite a),
      intervalPotentialCoefficients_ofFunction]
    exact dirichletPotentialCoefficients_congr_ae _ _ _ _ hbase
  have hsub : periodOneBoundaryPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a) =
      ⟨intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ),
        intervalPotentialCoefficients_mem _⟩ := Subtype.ext hcoeff
  change b.characteristic (by simp)
    (periodOneBoundaryPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val
    (periodOneBoundaryPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).property z = _
  have hc := congrArg (fun q : dirichletSubspace (p := 2) =>
    b.characteristic (by simp) q.val q.property z) hsub
  exact hc.trans (characteristic_eq_classicalSeparated b Φ hΦ z)

/-- The intrinsic source discriminant has the exact finite-input
classical monodromy value. -/
theorem canonicalDiscriminant_finite_eq_classical
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    canonicalDiscriminant (by simp)
      (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) z =
        classicalDiscriminant (finiteSourceCurve a) z := by
  exact canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _)
    (finiteSourceCurve a) (finiteSource_physical_compatibility a).1 z

/-- The unimodular classical identity transfers exactly to all three
normalized source functions on finite Hilbert input. -/
theorem sourceDiscriminant_sq_sub_four_finite
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    (canonicalDiscriminant (by simp)
      (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) z)^2-4 =
      (sourceAntiDiscriminantCandidate (by simp) (by norm_num)
        (CoeffPair.ofFinsupp (p := 2) a) z)^2 -
        4 * periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
          (CoeffPair.ofFinsupp (p := 2) a) z *
          periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann
            (CoeffPair.ofFinsupp (p := 2) a) z := by
  rw [canonicalDiscriminant_finite_eq_classical,
    sourceAntiDiscriminantCandidate_finite_eq_classical,
    periodOneBoundaryCharacteristic_finite_eq_classical .dirichlet,
    periodOneBoundaryCharacteristic_finite_eq_classical .neumann]
  exact classicalDiscriminant_sq_sub_four (finiteSourceCurve a) z

/-- The source discriminant is exponent compatible. -/
theorem sourceDiscriminant_exponent
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hq
        (periodOnePotential (CoeffPair.exponentInclusion h φ)) z := by
  rw [← periodOnePotential_exponent h φ]
  exact canonicalDiscriminant_exponent hp hq h (periodOnePotential φ) z

/-- The full source identity holds on finite Fourier pairs at every finite
Banach exponent greater than one. -/
theorem sourceDiscriminant_sq_sub_four_finite_of_exponent
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    (canonicalDiscriminant hp
      (periodOnePotential (CoeffPair.ofFinsupp (p := p) a)) z)^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1
        (CoeffPair.ofFinsupp (p := p) a) z)^2 -
        4 * periodOneBoundaryCharacteristic hp hp1 .dirichlet
          (CoeffPair.ofFinsupp (p := p) a) z *
          periodOneBoundaryCharacteristic hp hp1 .neumann
            (CoeffPair.ofFinsupp (p := p) a) z := by
  rcases le_total p 2 with h | h
  · have hΔ := sourceDiscriminant_exponent hp (by simp) h
      (CoeffPair.ofFinsupp (p := p) a) z
    have hδ := congrFun (sourceAntiDiscriminantCandidate_exponent hp (by simp)
      hp1 (by norm_num) h (CoeffPair.ofFinsupp (p := p) a)) z
    have hD := congrFun (periodOneBoundaryCharacteristic_exponent hp (by simp)
      hp1 (by norm_num) h .dirichlet (CoeffPair.ofFinsupp (p := p) a)) z
    have hN := congrFun (periodOneBoundaryCharacteristic_exponent hp (by simp)
      hp1 (by norm_num) h .neumann (CoeffPair.ofFinsupp (p := p) a)) z
    simp only [CoeffPair.exponentInclusion_ofFinsupp] at hΔ hδ hD hN
    rw [hΔ,hδ,hD,hN]
    exact sourceDiscriminant_sq_sub_four_finite a z
  · have hΔ := sourceDiscriminant_exponent (by simp) hp h
      (CoeffPair.ofFinsupp (p := 2) a) z
    have hδ := congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp
      (by norm_num) hp1 h (CoeffPair.ofFinsupp (p := 2) a)) z
    have hD := congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp
      (by norm_num) hp1 h .dirichlet (CoeffPair.ofFinsupp (p := 2) a)) z
    have hN := congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp
      (by norm_num) hp1 h .neumann (CoeffPair.ofFinsupp (p := 2) a)) z
    simp only [CoeffPair.exponentInclusion_ofFinsupp] at hΔ hδ hD hN
    rw [← hΔ,← hδ,← hD,← hN]
    exact sourceDiscriminant_sq_sub_four_finite a z

/-- The classical unimodular identity extends to the full finite-exponent
source space. It uses the actual-domain N−D anti-discriminant sign. -/
theorem sourceDiscriminant_sq_sub_four
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ z)^2 -
        4 * periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z *
          periodOneBoundaryCharacteristic hp hp1 .neumann φ z := by
  have hpair (ψ : CoeffPair p) : AnalyticAt ℂ
      (fun t : CoeffPair p => (z,t)) ψ := analyticAt_const.prod analyticAt_id
  have hΔ : Continuous (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t)) (hpair ψ)).continuousAt
  have hδ : Continuous (fun ψ : CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t)) (hpair ψ)).continuousAt
  have hD : Continuous (fun ψ : CoeffPair p =>
      periodOneBoundaryCharacteristic hp hp1 .dirichlet ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 .dirichlet
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t)) (hpair ψ)).continuousAt
  have hN : Continuous (fun ψ : CoeffPair p =>
      periodOneBoundaryCharacteristic hp hp1 .neumann ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 .neumann
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t)) (hpair ψ)).continuousAt
  have he := (denseRange_finiteSourcePairs hp).equalizer
    ((hΔ.pow 2).sub continuous_const)
    ((hδ.pow 2).sub ((continuous_const.mul hD).mul hN))
    (by funext a; exact sourceDiscriminant_sq_sub_four_finite_of_exponent hp hp1 a z)
  exact congrFun he φ

/-- Lemma 9.2(ii), strengthened to every Dirichlet eigenvalue: the
simple-eigenvalue hypothesis is unnecessary for this algebraic identity. -/
theorem sourceDiscriminant_sq_sub_four_at_dirichlet_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ)
    (hz : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z = 0) :
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ z)^2 := by
  rw [sourceDiscriminant_sq_sub_four hp hp1 φ z,hz]
  ring

/-- At every canonically indexed Dirichlet root `μₙ`, the source
anti-discriminant squares to the shifted discriminant, even when the root
is multiple. -/
theorem sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))^2 := by
  apply sourceDiscriminant_sq_sub_four_at_dirichlet_zero hp hp1
  apply (periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 .dirichlet φ _).mpr
  exact (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 .dirichlet φ _).mpr ⟨n,rfl⟩

end NLS.ZakharovShabat
