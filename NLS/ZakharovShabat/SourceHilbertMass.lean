import NLS.Poisson.SourceHamiltonianDirection
import NLS.ZakharovShabat.SourcePhaseCompatibility
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # The actual Hilbert source mass and its Hamiltonian direction

The reflected coefficient pairing is the holomorphic mass functional.
Its actual source cotangent generates opposite component phase rotations
with the dissertation's Poisson sign. On the real source form the mass
is exactly half the square of the original source-pair norm.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The original bilinear physical mass in source Fourier coefficients. -/
def sourceHilbertMass (φ : CoeffPair 2) : ℂ :=
  reflectedHilbertPairing φ.fst φ.snd

/-- Mass is an actual entire holomorphic quadratic source functional. -/
theorem analyticOnNhd_sourceHilbertMass : AnalyticOnNhd ℂ sourceHilbertMass univ := by
  intro φ _
  exact (reflectedHilbertPairing.analyticAt_bilinear _).comp₂
    ((WithLp.fstL 2 ℂ (Coeff 2) (Coeff 2)).analyticAt φ)
    ((WithLp.sndL 2 ℂ (Coeff 2) (Coeff 2)).analyticAt φ)

/-- The full mass cotangent differentiates both original components. -/
theorem fderiv_sourceHilbertMass_apply (φ h : CoeffPair 2) :
    (fderiv ℂ sourceHilbertMass φ) h =
      reflectedHilbertPairing φ.fst h.snd+reflectedHilbertPairing h.fst φ.snd := by
  have hd := reflectedHilbertPairing.hasFDerivAt_of_bilinear
    ((WithLp.fstL 2 ℂ (Coeff 2) (Coeff 2)).hasFDerivAt (x := φ))
    ((WithLp.sndL 2 ℂ (Coeff 2) (Coeff 2)).hasFDerivAt (x := φ))
  exact congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L h) hd.fderiv

private theorem reflectedHilbertPairing_single (a : Coeff 2) (n : ℤ) :
    reflectedHilbertPairing (lp.single 2 n 1) a = a (-n) := by
  simp [reflectedHilbertPairing_apply,lp.single_apply,Pi.single_apply]

@[simp] theorem cotangentCoefficients_sourceHilbertMass_fst (φ : CoeffPair 2) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num) (fderiv ℂ sourceHilbertMass φ)).1 n = φ.snd (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst,fderiv_sourceHilbertMass_apply]
  simp only [CoeffPair.inlCLM_fst,CoeffPair.inlCLM_snd,map_zero,zero_add]
  exact reflectedHilbertPairing_single _ _

@[simp] theorem cotangentCoefficients_sourceHilbertMass_snd (φ : CoeffPair 2) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num) (fderiv ℂ sourceHilbertMass φ)).2 n = φ.fst (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd,fderiv_sourceHilbertMass_apply]
  simp only [CoeffPair.inrCLM_fst,CoeffPair.inrCLM_snd,map_zero,zero_apply,add_zero]
  rw [reflectedHilbertPairing_comm]
  exact reflectedHilbertPairing_single _ _

/-- The actual mass Hamiltonian rotates the two original components
by opposite infinitesimal phases, with the original Poisson sign. -/
theorem sourceHamiltonianVector_sourceHilbertMass_eq_neg_sourcePhase (φ : CoeffPair 2) :
    sourceHamiltonianVector (by norm_num) sourceHilbertMass φ = -sourcePhase φ := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change -I*(CoeffPair.cotangentCoefficients (by norm_num) (fderiv ℂ sourceHilbertMass φ)).2 (-n) = _
    rw [cotangentCoefficients_sourceHilbertMass_snd]
    change -I*φ.fst (- -n) = -(I*φ.fst n)
    simp only [neg_neg]
    ring
  · ext n
    change I*(CoeffPair.cotangentCoefficients (by norm_num) (fderiv ℂ sourceHilbertMass φ)).1 (-n) = _
    rw [cotangentCoefficients_sourceHilbertMass_fst]
    change I*φ.snd (- -n) = -(-I*φ.snd n)
    simp only [neg_neg]
    ring

/-- On the actual real Hilbert source form, the holomorphic mass is
exactly half the squared original source norm. -/
theorem sourceHilbertMass_eq_half_norm_sq_of_realType
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    sourceHilbertMass φ = ((‖φ‖^2/2 : ℝ):ℂ) := by
  change ∀ n : ℤ, φ.snd n = conj (φ.fst (-n)) at hφ
  have hb : φ.snd = star (Coeff.reflection φ.fst) := by
    ext n
    change φ.snd n = conj (φ.fst (-n))
    exact hφ n
  have hnorm : ‖φ.snd‖ = ‖φ.fst‖ := by rw [hb,norm_star,Coeff.reflection.norm_map]
  have hpair := WithLp.prod_norm_sq_eq_of_L2 φ
  calc
    sourceHilbertMass φ = inner ℂ φ.fst φ.fst := by
      rw [sourceHilbertMass,reflectedHilbertPairing_apply,lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      have he := hφ (-n)
      simp only [neg_neg] at he
      rw [he]
      simp only [RCLike.inner_apply',starRingEnd_apply]
      ring
    _ = ((‖φ.fst‖^2 : ℝ):ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ((‖φ‖^2/2 : ℝ):ℂ) := by
      congr 1
      rw [hpair,hnorm]
      ring

end NLS.ZakharovShabat
