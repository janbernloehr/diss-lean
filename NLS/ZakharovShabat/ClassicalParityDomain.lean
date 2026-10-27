import NLS.Fourier.SignedIntervalH1Extension

/-! # Exact classical H¹ domains for the two periodicity signs -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The full original interval H¹ domain with a single signed endpoint condition. -/
structure HasClassicalParityDomain (r : ℤ) (f : ℝ → ℂ × ℂ) : Prop where
  fst_regular : HasIntervalH1Regularity (fun x => (f x).1)
  snd_regular : HasIntervalH1Regularity (fun x => (f x).2)
  boundary : f 1 = wave r 1 • f 0

/-- Repeat both original components with the same periodicity sign. -/
def parityIntervalExtension (r : ℤ) (f : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  (signedDouble (wave r 1) (fun t => (f t).1) x,
    signedDouble (wave r 1) (fun t => (f t).2) x)

theorem parityIntervalExtension_left (r : ℤ) (f : ℝ → ℂ × ℂ) {x : ℝ} (hx : x ≤ 1) :
    parityIntervalExtension r f x = f x := by simp [parityIntervalExtension,signedDouble_left _ _ hx]

theorem parityIntervalExtension_right (r : ℤ) (f : ℝ → ℂ × ℂ) {x : ℝ} (hx : 1 < x) :
    parityIntervalExtension r f x = wave r 1 • f (x-1) := by
  exact Prod.ext (signedDouble_right (wave r 1) (fun t => (f t).1) hx)
    (signedDouble_right (wave r 1) (fun t => (f t).2) hx)

/-- The actual weighted coefficients of a full classical signed interval domain vector. -/
def classicalParityExtension (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) : Domain 2 :=
  (signedSobolevCoefficients r (fun x => (f x).1) hf.fst_regular (congrArg Prod.fst hf.boundary),
    signedSobolevCoefficients r (fun x => (f x).2) hf.snd_regular (congrArg Prod.snd hf.boundary))

theorem classicalParityExtension_mem (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) : classicalParityExtension r f hf ∈ domainParitySubspace r := by
  intro n hn
  exact ⟨signedSobolevCoefficients_parity r _ hf.fst_regular (congrArg Prod.fst hf.boundary) n hn,
    signedSobolevCoefficients_parity r _ hf.snd_regular (congrArg Prod.snd hf.boundary) n hn⟩

/-- Fourier synthesis recovers the actual signed extension throughout the closed period. -/
theorem physicalDomain_classicalParityExtension (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    physicalDomain (classicalParityExtension r f hf) x = parityIntervalExtension r f x :=
  Prod.ext (sobolevSynthesis_signedSobolevCoefficients r _ hf.fst_regular (congrArg Prod.fst hf.boundary) hx)
    (sobolevSynthesis_signedSobolevCoefficients r _ hf.snd_regular (congrArg Prod.snd hf.boundary) hx)

/-- Restriction recovers all original interval values, including both endpoints. -/
theorem classicalParityExtension_restrict (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    physicalDomain (classicalParityExtension r f hf) x = f x := by
  rw [physicalDomain_classicalParityExtension r f hf ⟨hx.1,hx.2.trans (by norm_num)⟩,
    parityIntervalExtension_left r f hx.2]

/-- Every original one-derivative scalar Fourier vector has full interval H¹ regularity. -/
theorem intervalH1Regularity_sobolevSynthesis (a : ScalarDomain 2) :
    HasIntervalH1Regularity (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) := by
  constructor
  · exact (absolutelyContinuous_sobolevSynthesis a).mono (by
      simp only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),uIcc_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  · exact (memLp_deriv_sobolevSynthesis a).mono_measure
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by norm_num)))

/-- Every weighted parity vector restricts to the full classical domain with the correct sign. -/
theorem physicalDomain_mem_classicalParityDomain (r : ℤ) (a : Domain 2)
    (ha : a ∈ domainParitySubspace r) : HasClassicalParityDomain r (physicalDomain a) := by
  refine ⟨intervalH1Regularity_sobolevSynthesis a.1,intervalH1Regularity_sobolevSynthesis a.2,?_⟩
  simpa only [zero_add] using physicalDomain_add_one_of_parity a r ha 0

/-- The restriction of one parity domain is injective on the closed physical unit interval. -/
theorem physicalDomain_injective_on_unit_parity (r : ℤ) (a b : Domain 2)
    (ha : a ∈ domainParitySubspace r) (hb : b ∈ domainParitySubspace r)
    (h : EqOn (physicalDomain a) (physicalDomain b) (Icc 0 1)) : a = b := by
  apply sub_eq_zero.mp
  apply (physicalDomain_eq_zero_on_unit_iff (a-b) r ((domainParitySubspace r).sub_mem ha hb)).mp
  intro x hx
  have he : physicalDomain (a-b) x = physicalDomain a x - physicalDomain b x := by
    simp [physicalDomain,map_sub]
  rw [he,h hx,sub_self]
  rfl

/-- Extending the actual restriction recovers every original weighted parity vector. -/
@[simp] theorem classicalParityExtension_physicalDomain (r : ℤ) (a : Domain 2)
    (ha : a ∈ domainParitySubspace r) :
    classicalParityExtension r (physicalDomain a) (physicalDomain_mem_classicalParityDomain r a ha) = a := by
  apply physicalDomain_injective_on_unit_parity r _ a (classicalParityExtension_mem r _ _) ha
  intro x hx
  exact classicalParityExtension_restrict r _ _ hx

/-- Exactly the original parity-domain vectors arise from full classical signed H¹ functions. -/
theorem mem_domainParity_iff_exists_classicalParityExtension (r : ℤ) (a : Domain 2) :
    a ∈ domainParitySubspace r ↔
      ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f), classicalParityExtension r f hf = a := by
  constructor
  · intro ha
    exact ⟨physicalDomain a,physicalDomain_mem_classicalParityDomain r a ha,
      classicalParityExtension_physicalDomain r a ha⟩
  · rintro ⟨f,hf,rfl⟩
    exact classicalParityExtension_mem r f hf

/-- Two classical inputs give the same coefficients exactly when their interval values agree. -/
theorem classicalParityExtension_eq_iff (r : ℤ) (f g : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) (hg : HasClassicalParityDomain r g) :
    classicalParityExtension r f hf = classicalParityExtension r g hg ↔ EqOn f g (Icc 0 1) := by
  constructor
  · intro he x hx
    rw [← classicalParityExtension_restrict r f hf hx,← classicalParityExtension_restrict r g hg hx,he]
  · intro h
    apply physicalDomain_injective_on_unit_parity r _ _ (classicalParityExtension_mem r f hf)
      (classicalParityExtension_mem r g hg)
    intro x hx
    rw [classicalParityExtension_restrict r f hf hx,classicalParityExtension_restrict r g hg hx]
    exact h hx

end NLS.ZakharovShabat
