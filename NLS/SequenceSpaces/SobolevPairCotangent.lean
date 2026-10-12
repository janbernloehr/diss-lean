import NLS.SequenceSpaces.SobolevScalarGradient
import NLS.SequenceSpaces.WeightedPairNormInfty

/-! # Full two-component cotangents on every real Sobolev scale

Finite-p source pairs use the original component-sum norm. The two scalar
representatives retain the corrected physical index reversal and are
bounded in the component maximum norm. Subsequent target packaging uses
the separate source infinity norm when the conjugate exponent is infinity.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Reversing both signed first-component frequencies preserves the physical pairing. -/
theorem sobolevBilinearPairing_reflection (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevBilinearPairing s (reflection s a) (reflection (-s) b) = sobolevBilinearPairing s a b := by
  simp only [sobolevBilinearPairing_apply,reflection_apply]
  exact (Equiv.neg ℤ).tsum_eq (fun n => a.val n*b.val (-n))

end NLS.WeightedCoeff
namespace NLS.WeightedCoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Insert a raw first-component coefficient sequence in the source pair. -/
def inlCLM (w : Weight) : WeightedCoeff w p →L[ℂ] WeightedCoeffPair w p :=
  (toMax w p).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ _ _)

/-- Insert a raw second-component coefficient sequence in the source pair. -/
def inrCLM (w : Weight) : WeightedCoeff w p →L[ℂ] WeightedCoeffPair w p :=
  (toMax w p).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ _ _)

@[simp] theorem inlCLM_fst (w : Weight) (a : WeightedCoeff w p) : (inlCLM w a).fst = a := rfl
@[simp] theorem inlCLM_snd (w : Weight) (a : WeightedCoeff w p) : (inlCLM w a).snd = 0 := rfl
@[simp] theorem inrCLM_fst (w : Weight) (a : WeightedCoeff w p) : (inrCLM w a).fst = 0 := rfl
@[simp] theorem inrCLM_snd (w : Weight) (a : WeightedCoeff w p) : (inrCLM w a).snd = a := rfl

@[simp] theorem norm_inlCLM (w : Weight) (a : WeightedCoeff w p) : ‖inlCLM w a‖ = ‖a‖ :=
  WithLp.norm_toLp_fst p _ _ a
@[simp] theorem norm_inrCLM (w : Weight) (a : WeightedCoeff w p) : ‖inrCLM w a‖ = ‖a‖ :=
  WithLp.norm_toLp_snd p _ _ a

/-- Both scalar representatives, before selecting the conjugate pair norm. -/
def sobolevCotangentComponentsCLM (s : ℝ) (hp : p ≠ ⊤) :
    (WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :=
  ((WeightedCoeff.sobolevCotangentCLM s hp).comp
    ((ContinuousLinearMap.compL ℂ _ _ ℂ).flip (inlCLM (p := p) (Weight.sobolev s)))).prod
  ((WeightedCoeff.sobolevCotangentCLM s hp).comp
    ((ContinuousLinearMap.compL ℂ _ _ ℂ).flip (inrCLM (p := p) (Weight.sobolev s))))

@[simp] theorem sobolevCotangentComponentsCLM_fst (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    (sobolevCotangentComponentsCLM (q := q) s hp L).1 =
      WeightedCoeff.sobolevCotangent s hp (L.comp (inlCLM (Weight.sobolev s))) :=
  WeightedCoeff.sobolevCotangentCLM_apply s hp _

@[simp] theorem sobolevCotangentComponentsCLM_snd (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    (sobolevCotangentComponentsCLM (q := q) s hp L).2 =
      WeightedCoeff.sobolevCotangent s hp (L.comp (inrCLM (Weight.sobolev s))) :=
  WeightedCoeff.sobolevCotangentCLM_apply s hp _

/-- The component maximum is bounded by the original source operator norm. -/
theorem norm_sobolevCotangentComponentsCLM_le (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    ‖sobolevCotangentComponentsCLM (q := q) s hp L‖ ≤ ‖L‖ := by
  rw [Prod.norm_def,sobolevCotangentComponentsCLM_fst,sobolevCotangentComponentsCLM_snd,
    WeightedCoeff.norm_sobolevCotangent,WeightedCoeff.norm_sobolevCotangent]
  apply max_le
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inlCLM] using L.le_opNorm (inlCLM _ a)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inrCLM] using L.le_opNorm (inrCLM _ a)

/-- Pairing against both recovered components represents every source direction. -/
theorem sobolevBilinearPairing_cotangentComponents (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ)
    (h : WeightedCoeffPair (Weight.sobolev s) p) :
    WeightedCoeff.sobolevBilinearPairing s h.fst (sobolevCotangentComponentsCLM (q := q) s hp L).1 +
      WeightedCoeff.sobolevBilinearPairing s h.snd (sobolevCotangentComponentsCLM (q := q) s hp L).2 = L h := by
  rw [sobolevCotangentComponentsCLM_fst,sobolevCotangentComponentsCLM_snd,
    WeightedCoeff.sobolevBilinearPairing_sobolevCotangent,WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]
  change L (inlCLM _ h.fst) + L (inrCLM _ h.snd) = L h
  rw [← map_add]
  congr 1
  apply (toMax _ p).injective
  exact Prod.ext (by simp) (by simp)

/-- No other pair of opposite-order components represents the same functional. -/
theorem sobolevCotangentComponents_unique (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ)
    (a b : WeightedCoeff (Weight.sobolev (-s)) q)
    (hab : ∀ h : WeightedCoeffPair (Weight.sobolev s) p,
      WeightedCoeff.sobolevBilinearPairing s h.fst a + WeightedCoeff.sobolevBilinearPairing s h.snd b = L h) :
    (a,b) = sobolevCotangentComponentsCLM (q := q) s hp L := by
  apply Prod.ext
  · rw [sobolevCotangentComponentsCLM_fst]
    apply WeightedCoeff.sobolevBilinearPairing_flip_injective (p := p) s
    ext h
    change WeightedCoeff.sobolevBilinearPairing s h a =
      WeightedCoeff.sobolevBilinearPairing s h
        (WeightedCoeff.sobolevCotangent (q := q) s hp (L.comp (inlCLM (Weight.sobolev s))))
    rw [WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]
    have he := hab (inlCLM (Weight.sobolev s) h)
    simpa only [inlCLM_fst,inlCLM_snd,map_zero,zero_apply,add_zero,
      WeightedCoeff.sobolevBilinearPairing_sobolevCotangent,ContinuousLinearMap.comp_apply] using he
  · rw [sobolevCotangentComponentsCLM_snd]
    apply WeightedCoeff.sobolevBilinearPairing_flip_injective (p := p) s
    ext h
    change WeightedCoeff.sobolevBilinearPairing s h b =
      WeightedCoeff.sobolevBilinearPairing s h
        (WeightedCoeff.sobolevCotangent (q := q) s hp (L.comp (inrCLM (Weight.sobolev s))))
    rw [WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]
    have he := hab (inrCLM (Weight.sobolev s) h)
    simpa only [inrCLM_fst,inrCLM_snd,map_zero,zero_apply,zero_add,
      WeightedCoeff.sobolevBilinearPairing_sobolevCotangent,ContinuousLinearMap.comp_apply] using he

/-- The bounded functional associated with two opposite-order components. -/
def sobolevPairFunctional (s : ℝ)
    (a b : WeightedCoeff (Weight.sobolev (-s)) q) :
    WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ :=
  ((WeightedCoeff.sobolevBilinearPairing s).flip a).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (toMax (Weight.sobolev s) p).toContinuousLinearMap) +
  ((WeightedCoeff.sobolevBilinearPairing s).flip b).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (toMax (Weight.sobolev s) p).toContinuousLinearMap)

@[simp] theorem sobolevPairFunctional_apply (s : ℝ)
    (a b : WeightedCoeff (Weight.sobolev (-s)) q) (h : WeightedCoeffPair (Weight.sobolev s) p) :
    sobolevPairFunctional s a b h = WeightedCoeff.sobolevBilinearPairing s h.fst a +
      WeightedCoeff.sobolevBilinearPairing s h.snd b := rfl

end NLS.WeightedCoeffPair
