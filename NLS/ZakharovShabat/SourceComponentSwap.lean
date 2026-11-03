import NLS.ZakharovShabat.ClassicalComponentSwap
import NLS.ZakharovShabat.SourceDiscriminantExtension
import NLS.ZakharovShabat.SourceLemma9_1

/-! # Unsigned component swap on the original Fourier–Lebesgue source

The actual swap is an isometry and fixes exactly the mKdV coefficient
pairs with equal components. Spectral covariance is proved first on the
literal classical finite Fourier potentials and then by continuity in
all finite source exponents greater than one.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unsigned component exchange, without any reflection of the spatial variable. -/
def sourceComponentSwap : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  LinearIsometryEquiv.withLpProdComm p ℂ (Coeff p) (Coeff p)

@[simp] theorem sourceComponentSwap_fst (φ : CoeffPair p) :
    (sourceComponentSwap φ).fst = φ.snd := rfl

@[simp] theorem sourceComponentSwap_snd (φ : CoeffPair p) :
    (sourceComponentSwap φ).snd = φ.fst := rfl

@[simp] theorem sourceComponentSwap_involutive (φ : CoeffPair p) :
    sourceComponentSwap (sourceComponentSwap φ) = φ := by
  apply (CoeffPair.toMax p).injective
  exact Prod.swap_swap (CoeffPair.toMax p φ)

/-- The actual component exchange retains the conjugate-reflection real form. -/
theorem sourceComponentSwap_realType (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourceComponentSwap φ)) := by
  intro n
  change φ.fst n = conj (φ.snd (-n))
  have hn : φ.snd (-n) = conj (φ.fst (-(-n))) := hφ (-n)
  rw [hn,neg_neg]
  simp

/-- Its fixed points are precisely the coefficient diagonal used by mKdV. -/
theorem sourceComponentSwap_eq_self_iff (φ : CoeffPair p) :
    sourceComponentSwap φ = φ ↔ φ.fst = φ.snd := by
  constructor
  · intro h
    exact (congrArg (fun ψ : CoeffPair p => ψ.fst) h).symm
  · intro h
    apply (CoeffPair.toMax p).injective
    exact Prod.ext h.symm h

/-- Restriction of the actual component swap to the original real source. -/
def realSourceComponentSwap (φ : realTypeSourceSubmodule p) : realTypeSourceSubmodule p :=
  ⟨sourceComponentSwap φ.val,sourceComponentSwap_realType φ.val φ.property⟩

@[simp] theorem realSourceComponentSwap_val (φ : realTypeSourceSubmodule p) :
    (realSourceComponentSwap φ).val = sourceComponentSwap φ.val := rfl

@[simp] theorem realSourceComponentSwap_involutive (φ : realTypeSourceSubmodule p) :
    realSourceComponentSwap (realSourceComponentSwap φ) = φ := by
  apply Subtype.ext
  exact sourceComponentSwap_involutive φ.val

@[simp] theorem sourceComponentSwap_ofFinsupp (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceComponentSwap (CoeffPair.ofFinsupp (p := p) a) = CoeffPair.ofFinsupp a.swap := rfl

/-- Finite Fourier synthesis realizes the literal physical component exchange. -/
theorem finiteSourceCurve_componentSwap (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteSourceCurve a.swap = classicalComponentSwap (finiteSourceCurve a) := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The actual source discriminant transforms with spectral reflection
under unsigned component exchange, at every finite exponent p>1. -/
theorem sourceDiscriminant_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ)) (-z) =
      canonicalDiscriminant hp (periodOnePotential φ) z := by
  have hc : Continuous (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) (-z)) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (-z,ψ) (mem_univ _)).comp
      (f := fun t : CoeffPair p => (-z,t)) (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceDiscriminant_unique_continuous hp hp1 z
    (fun ψ => canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap ψ)) (-z))
    (hc.comp sourceComponentSwap.continuous) (by
      intro a
      rw [sourceComponentSwap_ofFinsupp,sourceDiscriminant_finite_eq_classical,
        finiteSourceCurve_componentSwap,classicalDiscriminant_componentSwap])
  exact congrFun he φ

/-- Dirichlet and Neumann characteristics exchange, with their exact sine
normalization and spectral reflection retained. -/
theorem sourceBoundaryCharacteristic_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b (sourceComponentSwap φ) (-z) =
      -periodOneBoundaryCharacteristic hp hp1 (componentSwapBoundary b) φ z := by
  have hc : Continuous (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ (-z)) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b (-z,ψ) (mem_univ _)).comp
      (f := fun t : CoeffPair p => (-z,t)) (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceBoundaryCharacteristic_unique_continuous hp hp1 (componentSwapBoundary b) z
    (fun ψ => -periodOneBoundaryCharacteristic hp hp1 b (sourceComponentSwap ψ) (-z))
    (hc.comp sourceComponentSwap.continuous).neg (by
      intro a
      rw [sourceComponentSwap_ofFinsupp,periodOneBoundaryCharacteristic_finite_eq_classical_all,
        finiteSourceCurve_componentSwap,classicalSeparatedCharacteristic_componentSwap,neg_neg])
  exact neg_eq_iff_eq_neg.mp (congrFun he φ)

/-- The actual source anti-discriminant changes sign with the same reflected
spectral argument; this is the sheet information needed by the angles. -/
theorem sourceAntiDiscriminant_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 (sourceComponentSwap φ) (-z) =
      -sourceAntiDiscriminantCandidate hp hp1 φ z := by
  have hc : Continuous (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ (-z)) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (-z,ψ) (mem_univ _)).comp
      (f := fun t : CoeffPair p => (-z,t)) (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceAntiDiscriminantCandidate_unique_continuous hp hp1 z
    (fun ψ => -sourceAntiDiscriminantCandidate hp hp1 (sourceComponentSwap ψ) (-z))
    (hc.comp sourceComponentSwap.continuous).neg (by
      intro a
      rw [sourceComponentSwap_ofFinsupp,sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent,
        finiteSourceCurve_componentSwap,classicalAntiDiscriminant_componentSwap,neg_neg])
  exact neg_eq_iff_eq_neg.mp (congrFun he φ)

/-- On the actual mKdV diagonal the discriminant is an even function of the
spectral parameter. This holds in the full finite-exponent source topology. -/
theorem sourceDiscriminant_even_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : φ.fst = φ.snd) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) (-z) =
      canonicalDiscriminant hp (periodOnePotential φ) z := by
  have h := sourceDiscriminant_componentSwap hp hp1 φ z
  rw [(sourceComponentSwap_eq_self_iff φ).mpr hφ] at h
  exact h

/-- The diagonal anti-discriminant is odd, with the original N-D sign. -/
theorem sourceAntiDiscriminant_odd_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : φ.fst = φ.snd) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 φ (-z) = -sourceAntiDiscriminantCandidate hp hp1 φ z := by
  have h := sourceAntiDiscriminant_componentSwap hp hp1 φ z
  rw [(sourceComponentSwap_eq_self_iff φ).mpr hφ] at h
  exact h

end NLS.ZakharovShabat
