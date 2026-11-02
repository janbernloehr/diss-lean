import NLS.MKdV.MiuraPositiveCartesianMap
import NLS.ZakharovShabat.SourceDiagonalActionRootInverse

/-! # A bounded inverse for the actual free Cartesian Jacobian

The inverse uses the positive coordinate pair to reconstruct the two
signed scalar Fourier coefficients. Its multiplier is bounded because
the physical half-order action roots are uniformly bounded away from
zero. The literal signed mean supplies the missing zero Fourier mode.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

def miuraFreeInverseSymbol : Coeff ⊤ := sourceDiagonalActionRootInverseSequence (0 : CoeffPair 2)

theorem miuraFreeInverseSymbol_nonpositive (n : ℤ) (hn : ¬0 < n) : miuraFreeInverseSymbol n = 0 := by
  let φ : realDiagonalSourceLocus 2 := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  simpa only [φ,miuraFreeInverseSymbol,if_neg hn] using sourceDiagonalActionRootInverseSequence_apply φ n

theorem miuraFreeInverseSymbol_scaled_mul (n : ℤ) (hn : 0 < n) :
    miuraFreeInverseSymbol n*((Weight.sobolev (1/2) n : ℂ)*
      sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)) = 1 := by
  let φ : realDiagonalSourceLocus 2 := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  exact sourceDiagonalActionRootInverseSequence_mul φ n hn

def miuraPositiveWeightedX : MiuraPositiveCartesianTarget →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (MiuraPositiveHalf.subtypeL.comp ((ContinuousLinearMap.fst ℂ MiuraPositiveHalf MiuraPositiveHalf).comp
      (ContinuousLinearMap.fst ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ)))

def miuraPositiveWeightedY : MiuraPositiveCartesianTarget →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (MiuraPositiveHalf.subtypeL.comp ((ContinuousLinearMap.snd ℂ MiuraPositiveHalf MiuraPositiveHalf).comp
      (ContinuousLinearMap.fst ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ)))

def miuraCartesianFreeInverse : MiuraPositiveCartesianTarget →L[ℂ] Coeff 2 :=
  let P := ((1/(Real.sqrt 2 : ℂ)) • (Coeff.multiplierCLM miuraFreeInverseSymbol)).comp
    (-miuraPositiveWeightedX+I • miuraPositiveWeightedY)
  let N := ((1/(Real.sqrt 2 : ℂ)) • (Coeff.multiplierCLM miuraFreeInverseSymbol)).comp
    (-miuraPositiveWeightedX-I • miuraPositiveWeightedY)
  P+Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp N+
    (ContinuousLinearMap.snd ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ).smulRight (lp.single 2 0 1)

theorem miuraCartesianFreeInverse_positive (z : MiuraPositiveCartesianTarget) (n : ℤ) (hn : 0 < n) :
    miuraCartesianFreeInverse z n = (miuraFreeInverseSymbol n*(Weight.sobolev (1/2) n : ℂ))*
      (-z.1.1.val.val n+I*z.1.2.val.val n)/(Real.sqrt 2 : ℂ) := by
  change (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol n*
      (-((Weight.sobolev (1/2) n : ℂ)*z.1.1.val.val n)+I*((Weight.sobolev (1/2) n : ℂ)*z.1.2.val.val n)))+
    (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol (-n)*
      (-((Weight.sobolev (1/2) (-n) : ℂ)*z.1.1.val.val (-n))-I*((Weight.sobolev (1/2) (-n) : ℂ)*z.1.2.val.val (-n))))+
    z.2*((lp.single 2 0 (1 : ℂ) : Coeff 2) n) = _
  rw [miuraFreeInverseSymbol_nonpositive (-n) (by omega)]
  have hsingle : (lp.single 2 0 (1 : ℂ) : Coeff 2) n = 0 := by simp [lp.single_apply,ne_of_gt hn]
  rw [hsingle]
  ring

theorem miuraCartesianFreeInverse_negative (z : MiuraPositiveCartesianTarget) (n : ℤ) (hn : 0 < n) :
    miuraCartesianFreeInverse z (-n) = (miuraFreeInverseSymbol n*(Weight.sobolev (1/2) n : ℂ))*
      (-z.1.1.val.val n-I*z.1.2.val.val n)/(Real.sqrt 2 : ℂ) := by
  change (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol (-n)*
      (-((Weight.sobolev (1/2) (-n) : ℂ)*z.1.1.val.val (-n))+I*((Weight.sobolev (1/2) (-n) : ℂ)*z.1.2.val.val (-n))))+
    (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol (-(-n))*
      (-((Weight.sobolev (1/2) (-(-n)) : ℂ)*z.1.1.val.val (-(-n)))-I*((Weight.sobolev (1/2) (-(-n)) : ℂ)*z.1.2.val.val (-(-n)))))+
    z.2*((lp.single 2 0 (1 : ℂ) : Coeff 2) (-n)) = _
  rw [miuraFreeInverseSymbol_nonpositive (-n) (by omega)]
  have hsingle : (lp.single 2 0 (1 : ℂ) : Coeff 2) (-n) = 0 := by simp [lp.single_apply,show -n ≠ 0 by omega]
  rw [hsingle]
  simp only [neg_neg]
  ring

theorem miuraCartesianFreeInverse_mean (z : MiuraPositiveCartesianTarget) : miuraCartesianFreeInverse z 0 = z.2 := by
  change (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol 0*
      (-((Weight.sobolev (1/2) 0 : ℂ)*z.1.1.val.val 0)+I*((Weight.sobolev (1/2) 0 : ℂ)*z.1.2.val.val 0)))+
    (1/(Real.sqrt 2 : ℂ))*(miuraFreeInverseSymbol (-0)*
      (-((Weight.sobolev (1/2) (-0) : ℂ)*z.1.1.val.val (-0))-I*((Weight.sobolev (1/2) (-0) : ℂ)*z.1.2.val.val (-0))))+
    z.2*((lp.single 2 0 (1 : ℂ) : Coeff 2) 0) = _
  simp [miuraFreeInverseSymbol_nonpositive 0 (by omega),lp.single_apply]

end NLS.MKdV
