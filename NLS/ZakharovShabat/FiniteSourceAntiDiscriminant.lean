import NLS.ZakharovShabat.ClassicalSeparatedCanonicalIdentity
import NLS.ZakharovShabat.ClassicalAuxiliarySpectralBridge
import NLS.ZakharovShabat.SourceAntiDiscriminantCandidate

/-!
# The source anti-discriminant on finite Fourier input

The normalized starred characteristic is identified with the actual
classical auxiliary monodromy characteristic on every finite source
polynomial. Their domain-based Neumann-minus-Dirichlet difference is then
the classical anti-discriminant, with the printed D/N label mismatch kept
explicit.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The rotated finite source has precisely the Dirichlet Fourier
coefficients of its rotated physical interval potential. -/
theorem auxiliaryPeriodOneDirichletPotential_finite_eq_classicalSourcePhase
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val =
      intervalPotentialCoefficients (intervalL2OfFunction
        (extend (classicalSourcePhase (finiteSourceCurve a)))
        (memLp_extend_classicalCurve _)) := by
  have hbase : BoundaryCondition.periodOnePair a =ᵐ[volume.restrict (Ioc 0 1)]
      extend (finiteSourceCurve a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (extend_finiteSourceCurve a x (Ioc_subset_Icc_self hx)).symm
  have hrot : physicalAuxiliaryPotential (BoundaryCondition.periodOnePair a) =ᵐ[
      volume.restrict (Ioc 0 1)] extend (classicalSourcePhase (finiteSourceCurve a)) := by
    filter_upwards [hbase] with x hx
    calc
      physicalAuxiliaryPotential (BoundaryCondition.periodOnePair a) x =
          physicalAuxiliaryPotential (extend (finiteSourceCurve a)) x := by
            simp only [physicalAuxiliaryPotential,hx]
      _ = extend (classicalSourcePhase (finiteSourceCurve a)) x :=
        congrFun (physicalAuxiliaryPotential_extend (finiteSourceCurve a)) x
  change auxiliaryPotential
      (auxiliaryPeriodOnePotential (by simp) (by norm_num)
        (CoeffPair.ofFinsupp (p := 2) a)).val = _
  rw [auxiliaryPeriodOnePotential_finite_eq a,
    auxiliaryPotential_neumannPotentialCoefficients]
  rw [intervalPotentialCoefficients_ofFunction]
  exact dirichletPotentialCoefficients_congr_ae _ _ _ _ hrot

/-- At finite Fourier input, each normalized actual starred product is the
corresponding classical auxiliary monodromy characteristic as a function,
not merely as a zero set. -/
theorem auxiliaryPeriodOneCharacteristic_finite_eq_classical
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b
      (CoeffPair.ofFinsupp (p := 2) a) z =
        classicalAuxiliaryCharacteristic b (finiteSourceCurve a) z := by
  let Φ := finiteSourceCurve a
  have hΦ : MemLp (extend (classicalSourcePhase Φ)) 2
      (volume.restrict (Ioc 0 1)) := memLp_extend_classicalCurve _
  have hcoeff := auxiliaryPeriodOneDirichletPotential_finite_eq_classicalSourcePhase a
  have hsub : auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a) =
      ⟨intervalPotentialCoefficients (intervalL2OfFunction
        (extend (classicalSourcePhase Φ)) hΦ),
        intervalPotentialCoefficients_mem _⟩ := Subtype.ext hcoeff
  change b.characteristic (by simp)
    (auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val
    (auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).property z = _
  have hc := congrArg (fun q : dirichletSubspace (p := 2) =>
    b.characteristic (by simp) q.val q.property z) hsub
  exact hc.trans ((characteristic_eq_classicalSeparated b (classicalSourcePhase Φ) hΦ z).trans
    (classicalAuxiliaryCharacteristic_eq_separated_phase b Φ z).symm)

/-- The source candidate equals the classical monodromy anti-trace on the
dense finite Fourier source. The N−D sign uses the actual endpoint domains. -/
theorem sourceAntiDiscriminantCandidate_finite_eq_classical
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a) z =
        classicalAntiDiscriminant (finiteSourceCurve a) z := by
  rw [sourceAntiDiscriminantCandidate,
    auxiliaryPeriodOneCharacteristic_finite_eq_classical .neumann a z,
    auxiliaryPeriodOneCharacteristic_finite_eq_classical .dirichlet a z]
  exact (classicalAntiDiscriminant_eq_auxiliary_sub (finiteSourceCurve a) z).symm

/-- The finite-source monodromy identity is independent of the finite
coefficient exponent used to embed the polynomial data. -/
theorem sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1
      (CoeffPair.ofFinsupp (p := p) a) z =
        classicalAntiDiscriminant (finiteSourceCurve a) z := by
  rcases le_total p 2 with h | h
  · have he := congrFun (sourceAntiDiscriminantCandidate_exponent hp
      (by simp) hp1 (by norm_num) h (CoeffPair.ofFinsupp (p := p) a)) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.trans (sourceAntiDiscriminantCandidate_finite_eq_classical a z)
  · have he := congrFun (sourceAntiDiscriminantCandidate_exponent
      (by simp) hp (by norm_num) hp1 h (CoeffPair.ofFinsupp (p := 2) a)) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.symm.trans (sourceAntiDiscriminantCandidate_finite_eq_classical a z)

/-- Finite Fourier source pairs are dense in every finite source Banach
space. -/
theorem denseRange_finiteSourcePairs {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    DenseRange (CoeffPair.ofFinsupp (p := p)) := by
  exact ((CoeffPair.toMax p).symm.surjective.denseRange.comp
    ((Coeff.denseRange_ofFinsupp hp).prodMap (Coeff.denseRange_ofFinsupp hp))
    (CoeffPair.toMax p).symm.continuous)

/-- At each spectral parameter, the source anti-discriminant is the unique
continuous extension of the classical monodromy anti-trace on finite
Fourier input. -/
theorem sourceAntiDiscriminantCandidate_unique_continuous
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (F : CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (CoeffPair.ofFinsupp (p := p) a) =
        classicalAntiDiscriminant (finiteSourceCurve a) z) :
    F = fun φ => sourceAntiDiscriminantCandidate hp hp1 φ z := by
  have hC : Continuous (fun φ : CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 φ z) := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    have hpair : AnalyticAt ℂ (fun ψ : CoeffPair p => (z,ψ)) φ :=
      analyticAt_const.prod analyticAt_id
    exact ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (z,ψ)) hpair).continuousAt
  apply (denseRange_finiteSourcePairs hp).equalizer hF hC
  funext a
  exact (hfinite a).trans
    (sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent hp hp1 a z).symm

end NLS.ZakharovShabat
