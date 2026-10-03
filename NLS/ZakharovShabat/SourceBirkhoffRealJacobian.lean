import NLS.ZakharovShabat.SourceBirkhoffJacobianInvertible
import NLS.ZakharovShabat.SourceRealTypeProjection

/-! # The real Birkhoff derivative

Differentiating the complex inclusion identifies the real derivative with
the restriction of the complex Jacobian. The real/imaginary decomposition
then transfers complex bijectivity to the actual real Banach spaces.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Differentiation commutes with the inclusion of the two real forms. -/
theorem real_jacobian_complex_inclusion
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ h : realTypeSourceSubmodule p) :
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
      (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ h) =
        sourceBirkhoffJacobian hp hp1 s φ.val h.val := by
  let inc := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  have hl := inc.hasFDerivAt.comp φ
    (D.real_map_analytic φ (mem_univ φ)).differentiableAt.hasFDerivAt
  have hr := ((D.analytic φ.val (D.real_subset φ.property)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp φ
    (realTypeSourceSubmodule p).subtypeL.hasFDerivAt
  have heq : (fun ψ => inc (sourceRealBirkhoffMap hp hp1 s ψ)) =
      (fun ψ : realTypeSourceSubmodule p => sourceBirkhoffMap hp hp1 s ψ.val) :=
    funext D.real_map_complex_inclusion
  change HasFDerivAt (fun ψ => inc (sourceRealBirkhoffMap hp hp1 s ψ)) _ φ at hl
  rw [heq] at hl
  exact congrArg (fun L => L h) (hl.unique hr)

/-- Bijectivity on the real source and real sequence spaces follows from
complex bijectivity, by splitting any complex preimage into real parts. -/
theorem real_jacobian_bijective_of_complex
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p)
    (hbij : Function.Bijective (sourceBirkhoffJacobian hp hp1 s φ.val)) :
    Function.Bijective (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ) := by
  let inc := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  let J := sourceBirkhoffJacobian hp hp1 s φ.val
  let R := fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ
  have hinc (h : realTypeSourceSubmodule p) : inc (R h) = J h.val :=
    D.real_jacobian_complex_inclusion φ h
  constructor
  · intro u v huv
    apply Subtype.ext
    apply hbij.1
    rw [← hinc, ← hinc, huv]
  · intro z
    obtain ⟨h, hh⟩ := hbij.2 (inc z)
    let u : realTypeSourceSubmodule p := ⟨sourceRealPart h, sourceRealPart_realType h⟩
    let v : realTypeSourceSubmodule p := ⟨sourceImagPart h, sourceImagPart_realType h⟩
    refine ⟨u, ?_⟩
    have hdec : inc (R u) + I • inc (R v) = inc z := by
      rw [hinc, hinc, ← map_smul, ← map_add]
      exact (congrArg J (sourceRealPart_add_I_smul_sourceImagPart h)).trans hh
    apply Prod.ext <;> ext n
    · have hn := congrArg (fun w : Coeff p × Coeff p => (w.1 n).re) hdec
      change (((R u).1 n : ℂ) + I * ((R v).1 n : ℂ)).re = z.1 n at hn
      simpa using hn
    · have hn := congrArg (fun w : Coeff p × Coeff p => (w.2 n).re) hdec
      change (((R u).2 n : ℂ) + I * ((R v).2 n : ℂ)).re = z.2 n at hn
      simpa using hn

/-- Real bijectivity at every exponent at least two. -/
theorem real_jacobian_bijective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    Function.Bijective (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ) :=
  D.real_jacobian_bijective_of_complex φ (D.jacobian_bijective h2p φ)

/-- The derivative of the real map as an actual bounded real equivalence. -/
def realJacobianEquiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    realTypeSourceSubmodule p ≃L[ℝ] (RealCoeff p × RealCoeff p) :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ)
    (LinearMap.ker_eq_bot.mpr (D.real_jacobian_bijective h2p φ).1)
    (LinearMap.range_eq_top.mpr (D.real_jacobian_bijective h2p φ).2)

@[simp] theorem realJacobianEquiv_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    (D.realJacobianEquiv h2p φ).toContinuousLinearMap =
      fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ := rfl

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
