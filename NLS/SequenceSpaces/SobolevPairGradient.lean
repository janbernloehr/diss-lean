import NLS.SequenceSpaces.SobolevPairCotangent

/-! # Pair gradients with the original finite and infinity norms

The conjugate finite norm and the separate frequencywise sum norm at infinity
are packaged separately. All finite source exponents are covered, including
the p=1 endpoint. Both gradients are bounded linear functions of the full
cotangent, unique under the corrected physical pairing, and analytic for
analytic scalar functionals.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Finite conjugate pair representation in the source's original q-sum norm. -/
def sobolevFiniteGradientCLM (s : ℝ) (hp : p ≠ ⊤) (_hq : q ≠ ⊤) :
    (WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) →L[ℂ]
      WeightedCoeffPair (Weight.sobolev (-s)) q :=
  (toMax (Weight.sobolev (-s)) q).symm.toContinuousLinearMap.comp
    (sobolevCotangentComponentsCLM s hp)

/-- A bound in the exact conjugate pair norm, with the original source operator norm. -/
theorem norm_sobolevFiniteGradientCLM_le (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    ‖sobolevFiniteGradientCLM s hp hq L‖ ≤ (2 : ℝ) ^ (1/q.toReal)*‖L‖ := by
  exact (norm_toMax_symm_le hq _ _).trans
    (mul_le_mul_of_nonneg_left (norm_sobolevCotangentComponentsCLM_le (q := q) s hp L) (by positivity))

/-- Recovery of the entire functional using the actual finite conjugate pair. -/
theorem sobolevFiniteGradient_represents (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ)
    (h : WeightedCoeffPair (Weight.sobolev s) p) :
    WeightedCoeff.sobolevBilinearPairing s h.fst (sobolevFiniteGradientCLM s hp hq L).fst +
      WeightedCoeff.sobolevBilinearPairing s h.snd (sobolevFiniteGradientCLM s hp hq L).snd = L h :=
  sobolevBilinearPairing_cotangentComponents s hp L h

/-- Unique finite conjugate pair representation, with no coordinate-density assumption on L. -/
theorem existsUnique_sobolevFiniteGradient (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    ∃! g : WeightedCoeffPair (Weight.sobolev (-s)) q,
      ∀ h : WeightedCoeffPair (Weight.sobolev s) p,
        WeightedCoeff.sobolevBilinearPairing s h.fst g.fst +
          WeightedCoeff.sobolevBilinearPairing s h.snd g.snd = L h := by
  refine ⟨sobolevFiniteGradientCLM s hp hq L,sobolevFiniteGradient_represents s hp hq L,?_⟩
  intro g hg
  apply (toMax (Weight.sobolev (-s)) q).injective
  exact sobolevCotangentComponents_unique s hp L g.fst g.snd hg

/-- Analytic dependence of the finite conjugate gradient on the base point. -/
theorem analyticOnNhd_sobolevFiniteGradient (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev s) p → ℂ)
    {U : Set (WeightedCoeffPair (Weight.sobolev s) p)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun x => sobolevFiniteGradientCLM s hp hq (fderiv ℂ F x)) U := by
  intro x hx
  exact ((sobolevFiniteGradientCLM s hp hq).analyticAt _).comp (hF.fderiv x hx)

/-- The finite conjugate representation also preserves the signed first-component convention. -/
theorem sobolevFiniteGradient_represents_physical (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ)
    (h : WeightedCoeffPair (Weight.sobolev s) p) :
    let g := sobolevFiniteGradientCLM s hp hq L
    WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s h.fst)
        (WeightedCoeff.reflection (-s) g.fst) +
      WeightedCoeff.sobolevBilinearPairing s h.snd g.snd = L h := by
  simpa only [WeightedCoeff.sobolevBilinearPairing_reflection] using
    sobolevFiniteGradient_represents s hp hq L h

end NLS.WeightedCoeffPair
namespace NLS.WeightedCoeffPair

/-- The p=1 gradient lies in the source's frequencywise sum-norm infinity space. -/
def sobolevOneGradientCLM (s : ℝ) :
    (WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ) →L[ℂ]
      WeightedCoeffPairInfty (Weight.sobolev (-s)) :=
  (WeightedCoeffPairInfty.toMax (Weight.sobolev (-s))).symm.toContinuousLinearMap.comp
    (sobolevCotangentComponentsCLM (p := 1) (q := ⊤) s (by simp))

/-- The original infinity pair norm is bounded by twice the original source operator norm. -/
theorem norm_sobolevOneGradientCLM_le (s : ℝ)
    (L : WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ) :
    ‖sobolevOneGradientCLM s L‖ ≤ 2*‖L‖ := by
  exact (WeightedCoeffPairInfty.norm_toMax_symm_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_sobolevCotangentComponentsCLM_le (q := ⊤) s (by simp) L) (by norm_num))

/-- The original p=1 functional is recovered on every source direction. -/
theorem sobolevOneGradient_represents (s : ℝ)
    (L : WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ)
    (h : WeightedCoeffPair (Weight.sobolev s) 1) :
    WeightedCoeff.sobolevBilinearPairing s h.fst (sobolevOneGradientCLM s L).1 +
      WeightedCoeff.sobolevBilinearPairing s h.snd (sobolevOneGradientCLM s L).2 = L h :=
  sobolevBilinearPairing_cotangentComponents s (by simp) L h

/-- Every p=1 source functional has a unique gradient in the stated infinity pair space. -/
theorem existsUnique_sobolevOneGradient (s : ℝ)
    (L : WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ) :
    ∃! g : WeightedCoeffPairInfty (Weight.sobolev (-s)),
      ∀ h : WeightedCoeffPair (Weight.sobolev s) 1,
        WeightedCoeff.sobolevBilinearPairing s h.fst g.1 +
          WeightedCoeff.sobolevBilinearPairing s h.snd g.2 = L h := by
  refine ⟨sobolevOneGradientCLM s L,sobolevOneGradient_represents s L,?_⟩
  intro g hg
  apply (WeightedCoeffPairInfty.toMax (Weight.sobolev (-s))).injective
  exact sobolevCotangentComponents_unique s (by simp) L g.1 g.2 hg

/-- Analytic p=1 functionals have analytic gradients in the original infinity pair norm. -/
theorem analyticOnNhd_sobolevOneGradient (s : ℝ)
    (F : WeightedCoeffPair (Weight.sobolev s) 1 → ℂ)
    {U : Set (WeightedCoeffPair (Weight.sobolev s) 1)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun x => sobolevOneGradientCLM s (fderiv ℂ F x)) U := by
  intro x hx
  exact ((sobolevOneGradientCLM s).analyticAt _).comp (hF.fderiv x hx)

/-- Exact raw signed coefficients of the endpoint gradient. -/
theorem sobolevOneGradient_coefficients (s : ℝ)
    (L : WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ) (n : ℤ) :
    (sobolevOneGradientCLM s L).1.val n = L (inlCLM (Weight.sobolev s)
      (WeightedCoeff.ofFinsupp (Weight.sobolev s) 1 (Finsupp.single (-n) 1))) ∧
    (sobolevOneGradientCLM s L).2.val n = L (inrCLM (Weight.sobolev s)
      (WeightedCoeff.ofFinsupp (Weight.sobolev s) 1 (Finsupp.single (-n) 1))) := by
  change (sobolevCotangentComponentsCLM (q := ⊤) s (by simp) L).1.val n = _ ∧
    (sobolevCotangentComponentsCLM (q := ⊤) s (by simp) L).2.val n = _
  simp only [sobolevCotangentComponentsCLM_fst,sobolevCotangentComponentsCLM_snd,
    WeightedCoeff.sobolevCotangent_val,ContinuousLinearMap.comp_apply,and_self]


/-- The endpoint representation in actual scalar Fourier coordinates: the first
signed component is reflected in both the source and the recovered gradient. -/
theorem sobolevOneGradient_represents_physical (s : ℝ)
    (L : WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ] ℂ)
    (h : WeightedCoeffPair (Weight.sobolev s) 1) :
    let g := WeightedCoeffPairInfty.toScalarMax (-s) (sobolevOneGradientCLM s L)
    WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s h.fst) g.1 +
      WeightedCoeff.sobolevBilinearPairing s h.snd g.2 = L h := by
  simpa only [WeightedCoeffPairInfty.toScalarMax_apply,
    WeightedCoeff.sobolevBilinearPairing_reflection] using sobolevOneGradient_represents s L h

/-- Recovery preserves any prescribed endpoint pair, with the original sum norm. -/
@[simp] theorem sobolevOneGradient_pairFunctional (s : ℝ)
    (a b : WeightedCoeff (Weight.sobolev (-s)) ⊤) :
    sobolevOneGradientCLM s (sobolevPairFunctional s a b) =
      WeightedCoeffPairInfty.ofPair (Weight.sobolev (-s)) a b := by
  apply (WeightedCoeffPairInfty.toMax (Weight.sobolev (-s))).injective
  exact (sobolevCotangentComponents_unique (p := 1) (q := ⊤) s (by simp)
    (sobolevPairFunctional s a b) a b (fun _ => rfl)).symm

/-- Equal endpoint components keep the source's factor two, including infinite support. -/
theorem norm_sobolevOneGradient_diagonal (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-s)) ⊤) :
    ‖sobolevOneGradientCLM s (sobolevPairFunctional s a a)‖ = 2*‖a‖ := by
  rw [sobolevOneGradient_pairFunctional,WeightedCoeffPairInfty.norm_diagonal]

end NLS.WeightedCoeffPair
