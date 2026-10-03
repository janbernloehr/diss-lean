import NLS.ZakharovShabat.SourceBirkhoffJacobianInvertible

/-! # Birkhoff Jacobian invertibility for every finite exponent above one

Below two, compatibility of the actual rectangular cotangents transports
a kernel vector into the Hilbert source space. Hilbert injectivity kills
that vector. Lemma 16.3 and the Fredholm alternative supply surjectivity.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual sequence-valued derivative commutes with exponent inclusion,
for any two constructed families; their root choices need not be identical. -/
theorem jacobian_exponent
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
    {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) (h : CoeffPair p) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceBirkhoffJacobian hp hp1 s φ.val h) =
    sourceBirkhoffJacobian hq hq1 t (CoeffPair.exponentInclusion hpq φ.val)
      (CoeffPair.exponentInclusion hpq h) := by
  have hd (n : ℤ) := D.angular.fderiv_birkhoffXY_exponent E.angular W V
    D.source_open E.source_open D.source_subset E.source_subset
    D.real_subset E.real_subset hpq n φ
  have he (n : ℤ) := E.jacobian_coordinates _
    (E.real_subset (realTypeSourceExponentInclusion hpq φ).property)
    (CoeffPair.exponentInclusion hpq h) n
  apply Prod.ext <;> ext n
  · change (sourceBirkhoffJacobian hp hp1 s φ.val h).1 n = _
    rw [(D.jacobian_coordinates φ.val (D.real_subset φ.property) h n).1, (hd n).1]
    exact (he n).1.symm
  · change (sourceBirkhoffJacobian hp hp1 s φ.val h).2 n = _
    rw [(D.jacobian_coordinates φ.val (D.real_subset φ.property) h n).2, (hd n).2]
    exact (he n).2.symm

/-- Hilbert injectivity transfers to every smaller source exponent. -/
theorem jacobian_injective_of_le_two
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    Function.Injective (sourceBirkhoffJacobian hp hp1 s φ.val) := by
  obtain ⟨V₀,C,V,t,E⟩ := exists_sourceBirkhoffMap_complex_analytic
    (p := 2) (by simp) (by norm_num)
  apply (injective_iff_map_eq_zero (sourceBirkhoffJacobian hp hp1 s φ.val)).mpr
  intro h hh
  apply CoeffPair.exponentInclusion_injective hp2
  have hi := (E.jacobian_bijective le_rfl (realTypeSourceExponentInclusion hp2 φ)).1
  apply hi
  have hz := D.jacobian_exponent E hp2 φ h
  rw [hh, map_zero] at hz
  exact hz.symm.trans (by simp)

/-- The full complex Jacobian is bijective for every `1 < p < ∞`. -/
theorem jacobian_bijective_all_exponents
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    Function.Bijective (sourceBirkhoffJacobian hp hp1 s φ.val) := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · exact D.jacobian_bijective h2p φ
  · have hi := D.jacobian_injective_of_le_two (le_of_not_ge h2p) φ
    have hni : Function.Injective (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val) :=
      (sourceBirkhoffFourierEquiv (p := p)).symm.injective.comp hi
    apply (sourceBirkhoffNormalizedJacobian_bijective_iff hp hp1 s φ.val).mp
    exact CompactSpectrum.bijective_of_injective_compact_sub_smul _ one_ne_zero
      (by simpa using D.isCompactOperator_normalizedJacobian_sub_id φ) hni

/-- Bounded complex inverse of the actual derivative throughout the full exponent range. -/
def jacobianEquivAll
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) : CoeffPair p ≃L[ℂ] (Coeff p × Coeff p) :=
  ContinuousLinearEquiv.ofBijective (sourceBirkhoffJacobian hp hp1 s φ.val)
    (LinearMap.ker_eq_bot.mpr (D.jacobian_bijective_all_exponents φ).1)
    (LinearMap.range_eq_top.mpr (D.jacobian_bijective_all_exponents φ).2)

@[simp] theorem jacobianEquivAll_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    (D.jacobianEquivAll φ).toContinuousLinearMap = sourceBirkhoffJacobian hp hp1 s φ.val := rfl

/-- An analytic local inverse of the complex Birkhoff map at every real
source in the range `1 < p < ∞`, with both actual inverse identities. -/
theorem exists_complex_localInverse_all_exponents
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ g : (Coeff p × Coeff p) → CoeffPair p,
      AnalyticAt ℂ g (sourceBirkhoffMap hp hp1 s φ.val) ∧
      g (sourceBirkhoffMap hp hp1 s φ.val) = φ.val ∧
      (∀ᶠ ψ in 𝓝 φ.val, g (sourceBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceBirkhoffMap hp hp1 s φ.val), sourceBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.jacobianEquivAll φ).symm.toContinuousLinearMap
        (sourceBirkhoffMap hp hp1 s φ.val) := by
  have ha := D.analytic φ.val (D.real_subset φ.property)
  have hd : HasStrictFDerivAt (sourceBirkhoffMap hp hp1 s)
      (D.jacobianEquivAll φ).toContinuousLinearMap φ.val :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (sourceBirkhoffMap hp hp1 s)
  have he : (e : CoeffPair p → (Coeff p × Coeff p)) = sourceBirkhoffMap hp hp1 s :=
    hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℂ e.symm (sourceBirkhoffMap hp hp1 s φ.val) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.jacobianEquivAll φ) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _, hg, hd.localInverse_apply_image,
    hd.eventually_left_inverse, hd.eventually_right_inverse, hd.to_localInverse⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
