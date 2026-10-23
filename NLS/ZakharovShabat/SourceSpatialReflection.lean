import NLS.ZakharovShabat.ClassicalSpatialReflection
import NLS.ZakharovShabat.SourceDiscriminantExtension
import NLS.ZakharovShabat.SourceLemma9_1
import NLS.SequenceSpaces.Reflection

/-! # Spatial reflection in the original source spaces

Frequency reversal and component swap define an involutive isometry of the
original source norm. Its action on the actual normalized spectral functions
is obtained from classical monodromy, first on finite Fourier data and then
by continuity on every finite exponent greater than one.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Midpoint reflection with component swap, in the original source norm. -/
def sourceSpatialReflection : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  (Coeff.reflection.withLpProdCongr p Coeff.reflection).trans
    (LinearIsometryEquiv.withLpProdComm p ℂ (Coeff p) (Coeff p))

@[simp] theorem sourceSpatialReflection_fst (φ : CoeffPair p) :
    (sourceSpatialReflection φ).fst = Coeff.reflection φ.snd := rfl

@[simp] theorem sourceSpatialReflection_snd (φ : CoeffPair p) :
    (sourceSpatialReflection φ).snd = Coeff.reflection φ.fst := rfl

@[simp] theorem sourceSpatialReflection_involutive (φ : CoeffPair p) :
    sourceSpatialReflection (sourceSpatialReflection φ) = φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp

/-- Reflection preserves the real-type locus. -/
theorem sourceSpatialReflection_realType (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourceSpatialReflection φ)) := by
  intro n
  change φ.fst (-n) = conj (φ.snd (-(-n)))
  have hn : φ.snd n = conj (φ.fst (-n)) := hφ n
  rw [neg_neg,hn]
  simp

/-- On real type the reflected first component is coefficientwise conjugation. -/
theorem sourceSpatialReflection_fst_realType (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (sourceSpatialReflection φ).fst n = conj (φ.fst n) := by
  simpa using hφ (-n)

/-- A real-type source is reflection fixed exactly when its first Fourier coefficients are real. -/
theorem sourceSpatialReflection_eq_self_iff (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    sourceSpatialReflection φ = φ ↔ ∀ n : ℤ, conj (φ.fst n) = φ.fst n := by
  constructor
  · intro h n
    simpa only [sourceSpatialReflection_fst_realType φ hφ] using
      congrArg (fun ψ : CoeffPair p => ψ.fst n) h
  · intro h
    apply (CoeffPair.toMax p).injective
    apply Prod.ext
    · ext n
      exact (sourceSpatialReflection_fst_realType φ hφ n).trans (h n)
    · ext n
      change φ.fst (-n) = φ.snd n
      exact (h (-n)).symm.trans (hφ n).symm

/-- The reflected finite pair uses the same reversal of integer Fourier indices. -/
def sourceReflectedFinitePair (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) :=
  (Finsupp.mapDomain (fun n : ℤ => -n) a.2,
    Finsupp.mapDomain (fun n : ℤ => -n) a.1)

@[simp] theorem sourceReflectedFinitePair_fst (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (sourceReflectedFinitePair a).1 n = a.2 (-n) := by
  change Finsupp.mapDomain (fun n : ℤ => -n) a.2 n = _
  simpa only [Equiv.neg_apply,neg_neg] using
    Finsupp.mapDomain_apply (Equiv.neg ℤ).injective a.2 (-n)

@[simp] theorem sourceReflectedFinitePair_snd (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (sourceReflectedFinitePair a).2 n = a.1 (-n) := by
  change Finsupp.mapDomain (fun n : ℤ => -n) a.1 n = _
  simpa only [Equiv.neg_apply,neg_neg] using
    Finsupp.mapDomain_apply (Equiv.neg ℤ).injective a.1 (-n)

@[simp] theorem sourceSpatialReflection_ofFinsupp (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceSpatialReflection (CoeffPair.ofFinsupp (p := p) a) =
      CoeffPair.ofFinsupp (sourceReflectedFinitePair a) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n <;> simp

private theorem reflected_polynomial (a b : ℤ →₀ ℂ)
    (h : ∀ n, b n = a (-n)) (t : ℝ) :
    polynomial b t = polynomial a (1-t) := by
  have hw (n : ℤ) : wave (2*n) (1-t) = wave (2*(-n)) t := by
    rw [sub_eq_add_neg,wave_add_argument,wave_even_at_one,one_mul]
    simp [wave]
  rw [polynomial_eq_tsum,polynomial_eq_tsum]
  simp only [h,hw]
  simpa only [Equiv.neg_apply,neg_neg] using
    (Equiv.neg ℤ).tsum_eq (fun n : ℤ => a n * wave (2*(-n)) t)

/-- The coefficient reflection is the literal classical midpoint reflection on finite input. -/
theorem finiteSourceCurve_reflected (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteSourceCurve (sourceReflectedFinitePair a) =
      classicalSpatialReflection (finiteSourceCurve a) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact reflected_polynomial a.2 (sourceReflectedFinitePair a).1
      (sourceReflectedFinitePair_fst a) t
  · exact reflected_polynomial a.1 (sourceReflectedFinitePair a).2
      (sourceReflectedFinitePair_snd a) t

/-- Reflection preserves the actual source discriminant at every spectral parameter. -/
theorem sourceDiscriminant_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (sourceSpatialReflection φ)) z =
      canonicalDiscriminant hp (periodOnePotential φ) z := by
  have hc : Continuous (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceDiscriminant_unique_continuous hp hp1 z
    (fun ψ => canonicalDiscriminant hp (periodOnePotential (sourceSpatialReflection ψ)) z)
    (hc.comp sourceSpatialReflection.continuous) (by
      intro a
      rw [sourceSpatialReflection_ofFinsupp,sourceDiscriminant_finite_eq_classical,
        finiteSourceCurve_reflected,classicalDiscriminant_spatialReflection])
  exact congrFun he φ

/-- Both actual separated characteristic functions are reflection invariant. -/
theorem sourceBoundaryCharacteristic_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b (sourceSpatialReflection φ) z =
      periodOneBoundaryCharacteristic hp hp1 b φ z := by
  have hc : Continuous (fun ψ : CoeffPair p =>
      periodOneBoundaryCharacteristic hp hp1 b ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceBoundaryCharacteristic_unique_continuous hp hp1 b z
    (fun ψ => periodOneBoundaryCharacteristic hp hp1 b (sourceSpatialReflection ψ) z)
    (hc.comp sourceSpatialReflection.continuous) (by
      intro a
      rw [sourceSpatialReflection_ofFinsupp,periodOneBoundaryCharacteristic_finite_eq_classical_all,
        finiteSourceCurve_reflected,classicalSeparatedCharacteristic_spatialReflection])
  exact congrFun he φ

/-- Reflection negates the anti-discriminant with its actual N−D convention. -/
theorem sourceAntiDiscriminant_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 (sourceSpatialReflection φ) z =
      -sourceAntiDiscriminantCandidate hp hp1 φ z := by
  have hc : Continuous (fun ψ : CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
      (z,ψ) (mem_univ _)).comp (f := fun t : CoeffPair p => (z,t))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceAntiDiscriminantCandidate_unique_continuous hp hp1 z
    (fun ψ => -sourceAntiDiscriminantCandidate hp hp1 (sourceSpatialReflection ψ) z)
    (hc.comp sourceSpatialReflection.continuous).neg (by
      intro a
      rw [sourceSpatialReflection_ofFinsupp,sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent,
        finiteSourceCurve_reflected,classicalAntiDiscriminant_spatialReflection,neg_neg])
  exact neg_eq_iff_eq_neg.mp (congrFun he φ)

end NLS.ZakharovShabat
