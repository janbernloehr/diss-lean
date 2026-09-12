import NLS.ZakharovShabat.ClassicalIntervalExtension

/-!
# Restriction of the weighted boundary domains

Weighted Dirichlet and Neumann pairs restrict to the original classical endpoint
domains. Extension and restriction are inverse, where original functions are
identified only on `[0,1]`. These are the set-theoretic domain identifications in
Lemma 4.2; comparison with physical Sobolev norms is a separate step.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The physical representative of a weighted pair, to be restricted to `[0,1]`. -/
def classicalIntervalRestriction (a : Domain 2) (x : ℝ) : ℂ × ℂ :=
  (sobolevSynthesis (by simp) a.1 (x : AddCircle (2 : ℝ)),
    sobolevSynthesis (by simp) a.2 (x : AddCircle (2 : ℝ)))

/-- The selected boundary domain is precisely a signed frequency-reflection graph. -/
theorem mem_domain_iff_reflection (b : BoundaryCondition) (a : Domain 2) :
    a ∈ domain b ↔ a.1 = extensionSign b • WeightedCoeff.reflection 1 a.2 := by
  cases b <;>
    simp only [domain, mem_weightedDirichletSubspace, mem_weightedNeumannSubspace,
      extensionSign, one_smul, neg_one_smul]
  · constructor
    · intro h
      apply Subtype.ext
      funext n
      simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using h n
    · intro h n
      simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using
        congrArg (fun c : ScalarDomain 2 => c.val n) h
  · constructor
    · intro h
      apply Subtype.ext
      funext n
      simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using h n
    · intro h n
      simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using
        congrArg (fun c : ScalarDomain 2 => c.val n) h

/-- The frequency graph gives the signed reflection identity at every physical point. -/
theorem classicalIntervalRestriction_reflection (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) (x : ℝ) :
    (classicalIntervalRestriction a x).1 =
      extensionSign b * (classicalIntervalRestriction a (2 - x)).2 := by
  change sobolevSynthesis (by simp) a.1 (x : AddCircle (2 : ℝ)) = _
  rw [(mem_domain_iff_reflection b a).mp ha, map_smul]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, sobolevSynthesis_reflection,
    classicalIntervalRestriction]

private theorem interval_regular (a : ScalarDomain 2) :
    HasIntervalH1Regularity (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) := by
  constructor
  · exact (absolutelyContinuous_sobolevSynthesis a).mono (by
      simp only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
        uIcc_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  · exact (memLp_deriv_sobolevSynthesis a).mono_measure
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by norm_num)))

/-- Restriction satisfies classical `H¹` regularity and both original endpoint conditions. -/
theorem classicalIntervalRestriction_mem (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) : HasClassicalIntervalDomain b (classicalIntervalRestriction a) := by
  refine ⟨interval_regular a.1, interval_regular a.2, ?_, ?_⟩
  · have h := congrArg (sobolevTrace (by simp) 0) ((mem_domain_iff_reflection b a).mp ha)
    rw [map_smul, sobolevTrace_reflection_zero] at h
    exact h
  · have h := congrArg (sobolevTrace (by simp) 1) ((mem_domain_iff_reflection b a).mp ha)
    rw [map_smul, sobolevTrace_reflection_one] at h
    exact h

/-- Folding the restricted representative recovers the whole physical period. -/
theorem intervalExtension_classicalIntervalRestriction (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) (x : ℝ) :
    intervalExtension b (classicalIntervalRestriction a) x = classicalIntervalRestriction a x := by
  by_cases hx : x ≤ 1
  · exact intervalExtension_left b _ x hx
  · rw [intervalExtension_right b _ x (lt_of_not_ge hx)]
    apply Prod.ext
    · exact (classicalIntervalRestriction_reflection b a ha x).symm
    · change extensionSign b * (classicalIntervalRestriction a (2 - x)).1 = _
      rw [classicalIntervalRestriction_reflection b a ha (2 - x),
        show 2 - (2 - x) = x by ring, ← mul_assoc, extensionSign_sq, one_mul]

/-- Extending the restriction recovers every weighted boundary pair. -/
@[simp] theorem classicalIntervalExtension_classicalIntervalRestriction (b : BoundaryCondition)
    (a : Domain 2) (ha : a ∈ domain b) :
    classicalIntervalExtension b (classicalIntervalRestriction a)
      (classicalIntervalRestriction_mem b a ha) = a := by
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · rw [classicalIntervalExtension_fst]
    simp only [intervalExtension_classicalIntervalRestriction b a ha,
      classicalIntervalRestriction, periodTwoCoefficient_sobolevSynthesis]
  · rw [classicalIntervalExtension_snd]
    simp only [intervalExtension_classicalIntervalRestriction b a ha,
      classicalIntervalRestriction, periodTwoCoefficient_sobolevSynthesis]

/-- Every element of the weighted boundary domain comes from an original classical pair. -/
theorem mem_domain_iff_exists_classicalIntervalExtension (b : BoundaryCondition) (a : Domain 2) :
    a ∈ domain b ↔ ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f),
      classicalIntervalExtension b f hf = a := by
  constructor
  · intro ha
    exact ⟨classicalIntervalRestriction a, classicalIntervalRestriction_mem b a ha,
      classicalIntervalExtension_classicalIntervalRestriction b a ha⟩
  · rintro ⟨f, hf, rfl⟩
    exact classicalIntervalExtension_mem b f hf

/-- Values outside the original interval do not affect its weighted extension. -/
theorem classicalIntervalExtension_congr (b : BoundaryCondition) (f g : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hg : HasClassicalIntervalDomain b g)
    (hfg : EqOn f g (Icc 0 1)) :
    classicalIntervalExtension b f hf = classicalIntervalExtension b g hg := by
  have he : EqOn (intervalExtension b f) (intervalExtension b g) (Icc 0 2) := by
    intro x hx
    by_cases hx1 : x ≤ 1
    · rw [intervalExtension_left b f x hx1, intervalExtension_left b g x hx1]
      exact hfg ⟨hx.1, hx1⟩
    · rw [intervalExtension_right b f x (lt_of_not_ge hx1),
        intervalExtension_right b g x (lt_of_not_ge hx1), hfg (show 2 - x ∈ Icc (0 : ℝ) 1 by
          constructor <;> linarith [hx.2])]
  have hc (j : ℂ × ℂ → ℂ) (n : ℤ) :
      periodTwoCoefficient (fun x => j (intervalExtension b f x)) n =
        periodTwoCoefficient (fun x => j (intervalExtension b g x)) n := by
    unfold periodTwoCoefficient
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [he (by simpa using hx)]
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · simpa only [classicalIntervalExtension_fst] using hc Prod.fst n
  · simpa only [classicalIntervalExtension_snd] using hc Prod.snd n

/-- Equality of extensions is exactly equality on the original closed interval. -/
theorem classicalIntervalExtension_eq_iff (b : BoundaryCondition) (f g : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hg : HasClassicalIntervalDomain b g) :
    classicalIntervalExtension b f hf = classicalIntervalExtension b g hg ↔
      EqOn f g (Icc 0 1) :=
  ⟨classicalIntervalExtension_injective_on_interval b f g hf hg,
    classicalIntervalExtension_congr b f g hf hg⟩

/-- Restriction distinguishes all weighted pairs in the selected boundary domain. -/
theorem classicalIntervalRestriction_injective_on_domain (b : BoundaryCondition)
    (a c : Domain 2) (ha : a ∈ domain b) (hc : c ∈ domain b)
    (h : EqOn (classicalIntervalRestriction a) (classicalIntervalRestriction c) (Icc 0 1)) :
    a = c := by
  have he := classicalIntervalExtension_congr b _ _
    (classicalIntervalRestriction_mem b a ha) (classicalIntervalRestriction_mem b c hc) h
  rw [classicalIntervalExtension_classicalIntervalRestriction b a ha,
    classicalIntervalExtension_classicalIntervalRestriction b c hc] at he
  exact he

/-- Every original classical endpoint pair has a unique weighted boundary representative. -/
theorem existsUnique_classicalIntervalRepresentative (b : BoundaryCondition)
    (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f) :
    ∃! a : Domain 2, a ∈ domain b ∧ EqOn (classicalIntervalRestriction a) f (Icc 0 1) := by
  refine ⟨classicalIntervalExtension b f hf, ⟨classicalIntervalExtension_mem b f hf, ?_⟩, ?_⟩
  · intro x hx
    exact classicalIntervalExtension_restrict b f hf hx
  · intro a ha
    apply classicalIntervalRestriction_injective_on_domain b a _ ha.1
      (classicalIntervalExtension_mem b f hf)
    intro x hx
    exact (ha.2 hx).trans (classicalIntervalExtension_restrict b f hf hx).symm

end NLS.ZakharovShabat.BoundaryCondition
