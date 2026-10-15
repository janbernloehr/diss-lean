import NLS.ZakharovShabat.PeriodOneSobolevMomentum
import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.Poisson.SourceHamiltonianDirection

/-! # The physical momentum cotangent on the entire complex H¹ space

Integration by parts moves the derivative off the variation. The resulting
Hilbert cotangent depends boundedly and complex linearly on the H¹ source.
Its actual source Hamiltonian direction is the period-one spatial derivative.
No real-type or finite-gap hypothesis is needed.
-/
noncomputable section
open Complex
namespace NLS.ZakharovShabat
open Poisson

/-- Periodic integration by parts for the physical bilinear L² pairing. -/
theorem reflectedHilbertPairing_periodOneDerivative (a b : ScalarDomain 2) :
    reflectedHilbertPairing (scalarInclusion a) (periodOneDerivative b) =
      -reflectedHilbertPairing (periodOneDerivative a) (scalarInclusion b) := by
  simp only [reflectedHilbertPairing_apply, ← tsum_neg]
  apply tsum_congr
  intro n
  simp only [scalarInclusion_apply, periodOneDerivative_apply, Int.cast_neg]
  ring

theorem periodOneSobolevMomentum_eq_reflectedPairing (a : ScalarDomain 2 × ScalarDomain 2) :
    periodOneSobolevMomentum a =
      -I * reflectedHilbertPairing (scalarInclusion a.1) (periodOneDerivative a.2) := by
  rw [reflectedHilbertPairing_comm]
  simp only [periodOneSobolevMomentum, Coeff.dualPairing_apply,
    Coeff.reflection_apply, reflectedHilbertPairing_apply, mul_comm]

/-- The L² cotangent of physical momentum, including its reflected Fourier indices. -/
def sourceSobolevMomentumCotangent : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ]
    (CoeffPair 2 →L[ℂ] ℂ) :=
  (-I) • reflectedHilbertPairing.bilinearComp
    (periodOneDerivative.comp (ContinuousLinearMap.snd ℂ _ _))
    ((ContinuousLinearMap.fst ℂ _ _).comp (CoeffPair.toMax 2).toContinuousLinearMap) +
  I • reflectedHilbertPairing.bilinearComp
    (periodOneDerivative.comp (ContinuousLinearMap.fst ℂ _ _))
    ((ContinuousLinearMap.snd ℂ _ _).comp (CoeffPair.toMax 2).toContinuousLinearMap)

@[simp] theorem sourceSobolevMomentumCotangent_apply
    (a : ScalarDomain 2 × ScalarDomain 2) (h : CoeffPair 2) :
    sourceSobolevMomentumCotangent a h =
      -I * reflectedHilbertPairing (periodOneDerivative a.2) h.fst +
        I * reflectedHilbertPairing (periodOneDerivative a.1) h.snd := rfl

/-- This is the full complex H¹ derivative of the independently defined physical momentum. -/
theorem hasFDerivAt_periodOneSobolevMomentum (a : ScalarDomain 2 × ScalarDomain 2) :
    HasFDerivAt periodOneSobolevMomentum
      ((sourceSobolevMomentumCotangent a).comp sobolevSourceInclusion) a := by
  let A := scalarInclusion.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))
  let B := periodOneDerivative.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))
  have hd := (reflectedHilbertPairing.hasFDerivAt_of_bilinear
    (A.hasFDerivAt (x := a)) (B.hasFDerivAt (x := a))).const_smul (-I)
  convert! hd using 1
  · funext b
    exact periodOneSobolevMomentum_eq_reflectedPairing b
  · apply ContinuousLinearMap.ext
    intro h
    change -I * reflectedHilbertPairing (periodOneDerivative a.2) (scalarInclusion h.1) +
        I * reflectedHilbertPairing (periodOneDerivative a.1) (scalarInclusion h.2) =
      -I * (reflectedHilbertPairing (scalarInclusion a.1) (periodOneDerivative h.2) +
        reflectedHilbertPairing (scalarInclusion h.1) (periodOneDerivative a.2))
    rw [reflectedHilbertPairing_periodOneDerivative, reflectedHilbertPairing_comm
      (scalarInclusion h.1)]
    ring

theorem fderiv_periodOneSobolevMomentum (a : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ periodOneSobolevMomentum a =
      (sourceSobolevMomentumCotangent a).comp sobolevSourceInclusion :=
  (hasFDerivAt_periodOneSobolevMomentum a).fderiv

/-- H¹ variations determine a Hilbert cotangent uniquely. -/
theorem sourceSobolevMomentumCotangent_unique (a : ScalarDomain 2 × ScalarDomain 2)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt periodOneSobolevMomentum (L.comp sobolevSourceInclusion) a) :
    L = sourceSobolevMomentumCotangent a := by
  have hd : DenseRange sobolevSourceInclusion :=
    (CoeffPair.toMax 2).symm.surjective.denseRange.comp
      ((scalarInclusion_denseRange (p := 2) (by simp)).prodMap
        (scalarInclusion_denseRange (p := 2) (by simp))) (CoeffPair.toMax 2).symm.continuous
  have he := hL.unique (hasFDerivAt_periodOneSobolevMomentum a)
  apply ContinuousLinearMap.ext
  exact congrFun (hd.equalizer L.continuous (sourceSobolevMomentumCotangent a).continuous
    (by funext h; exact congrArg (fun M : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ℂ => M h) he))

/-- The physical period-one derivative as a Hilbert source pair. -/
def sourceSobolevSpatialDerivative : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] CoeffPair 2 :=
  (CoeffPair.toMax 2).symm.toContinuousLinearMap.comp
    (periodOneDerivative.prodMap periodOneDerivative)

@[simp] theorem sourceSobolevSpatialDerivative_fst (a : ScalarDomain 2 × ScalarDomain 2) :
    (sourceSobolevSpatialDerivative a).fst = periodOneDerivative a.1 := rfl

@[simp] theorem sourceSobolevSpatialDerivative_snd (a : ScalarDomain 2 × ScalarDomain 2) :
    (sourceSobolevSpatialDerivative a).snd = periodOneDerivative a.2 := rfl

theorem sourceSobolevMomentumCotangent_coefficients (a : ScalarDomain 2 × ScalarDomain 2) :
    CoeffPair.cotangentCoefficients le_rfl (sourceSobolevMomentumCotangent a) =
      ((-I) • Coeff.reflection (periodOneDerivative a.2),
        I • Coeff.reflection (periodOneDerivative a.1)) := by
  apply Prod.ext
  · ext n
    rw [CoeffPair.cotangentCoefficients_fst]
    change sourceSobolevMomentumCotangent a (CoeffPair.inlCLM (lp.single 2 n 1)) =
      -I * periodOneDerivative a.2 (-n)
    simp [reflectedHilbertPairing_apply, lp.single_apply, Pi.single_apply,
      mul_ite, neg_eq_iff_eq_neg]
  · ext n
    rw [CoeffPair.cotangentCoefficients_snd]
    change sourceSobolevMomentumCotangent a (CoeffPair.inrCLM (lp.single 2 n 1)) =
      I * periodOneDerivative a.1 (-n)
    simp [reflectedHilbertPairing_apply, lp.single_apply, Pi.single_apply,
      mul_ite, neg_eq_iff_eq_neg]

/-- The original Poisson signs give positive spatial translation in both components. -/
theorem sourceHamiltonianDirection_momentum (a : ScalarDomain 2 × ScalarDomain 2) :
    sourceHamiltonianDirection le_rfl (sourceSobolevMomentumCotangent a) =
      sourceSobolevSpatialDerivative a := by
  rw [sourceHamiltonianDirection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, sourceSobolevMomentumCotangent_coefficients]
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change -I * (I * periodOneDerivative a.1 (- -n)) = periodOneDerivative a.1 n
    simp [← mul_assoc]
  · ext n
    change I * (-I * periodOneDerivative a.2 (- -n)) = periodOneDerivative a.2 n
    simp [← mul_assoc]

/-- Any Hilbert cotangent's momentum bracket is its evaluation on the spatial derivative. -/
theorem sourceBivector_momentum (a : ScalarDomain 2 × ScalarDomain 2)
    (L : CoeffPair 2 →L[ℂ] ℂ) :
    sourceBivector le_rfl L (sourceSobolevMomentumCotangent a) =
      L (sourceSobolevSpatialDerivative a) := by
  rw [← apply_sourceHamiltonianDirection, sourceHamiltonianDirection_momentum]

end NLS.ZakharovShabat
