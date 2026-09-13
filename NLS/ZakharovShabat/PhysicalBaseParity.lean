import NLS.ZakharovShabat.PhysicalParity
import NLS.Fourier.CircleTranslation

/-!
# Unit-interval uniqueness for physical parity base vectors

The almost-everywhere physical representative of a parity-supported Hilbert
coefficient vector has the same unit-translation multiplier as its Sobolev
domain counterpart. Thus vanishing on the unit interval determines the whole
base vector. This allows an original parity eigen-equation to be checked there.
-/

noncomputable section
open Set MeasureTheory NLS.Fourier
namespace NLS.Fourier

/-- Translation of a parity-supported Hilbert Fourier series is multiplication by its unit phase. -/
theorem circleTranslation_one_of_parity (a : Coeff 2) (r : ℤ)
    (ha : ∀ n : ℤ, n%2 ≠ r%2 → a n = 0) :
    circleTranslation 1 (l2Synthesis a) = wave r 1 • l2Synthesis a := by
  apply fourierBasis.repr.injective
  rw [map_smul]
  ext n
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,fourierBasis_repr]
  rw [fourierCoeff_circleTranslation,fourierCoeff_l2Synthesis]
  by_cases hn : n%2 = r%2
  · rw [wave_one_eq_mod n,hn,← wave_one_eq_mod r]
  · rw [ha n hn]
    simp

/-- The actual Hilbert representative obeys the parity translation law almost everywhere. -/
theorem circlePullback_add_one_of_parity (a : Coeff 2) (r : ℤ)
    (ha : ∀ n : ℤ, n%2 ≠ r%2 → a n = 0) :
    (fun x => circlePullback (l2Synthesis a) (x+1)) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => wave r 1 * circlePullback (l2Synthesis a) x) := by
  have ht := circlePullback_circleTranslation 1 (l2Synthesis a)
  rw [circleTranslation_one_of_parity a r ha] at ht
  have hs := circle_ae_pullback (Lp.coeFn_smul (wave r 1) (l2Synthesis a))
  filter_upwards [ht,hs] with x htx hsx
  simpa only [circlePullback,Pi.smul_apply,smul_eq_mul,add_comm] using htx.symm.trans hsx

end NLS.Fourier
namespace NLS.ZakharovShabat

/-- Both components of an original physical parity base vector retain the unit phase. -/
theorem physicalBase_add_one_of_parity (a : PairSpace 2) (r : ℤ)
    (ha : a ∈ pairParitySubspace r) :
    (fun x => physicalBase a (x+1)) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => wave r 1 • physicalBase a x) := by
  filter_upwards [circlePullback_add_one_of_parity a.1 r ((Coeff.mem_paritySubspace r a.1).mp ha.1),
    circlePullback_add_one_of_parity a.2 r ((Coeff.mem_paritySubspace r a.2).mp ha.2)] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- A parity base vector vanishing almost everywhere on the unit interval is zero. -/
theorem pairParity_eq_zero_of_physicalBase_unit (a : PairSpace 2) (r : ℤ)
    (ha : a ∈ pairParitySubspace r)
    (hz : physicalBase a =ᵐ[volume.restrict (Ioc 0 1)] (0 : ℝ → ℂ × ℂ)) : a = 0 := by
  have ht := physicalBase_add_one_of_parity a r ha
  simp only [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at ht hz
  have hfirst : ∀ᵐ x : ℝ, x ∈ Ioc (0 : ℝ) 1 → physicalBase a (x+1) = 0 := by
    filter_upwards [ht,hz] with x htx hzx
    intro hx
    rw [htx ⟨hx.1,hx.2.trans (by norm_num)⟩,hzx hx,Pi.zero_apply,smul_zero]
  have hsecond := (measurePreserving_add_right volume (-1 : ℝ)).quasiMeasurePreserving.ae hfirst
  apply physicalBase_injective a 0
  apply Filter.EventuallyEq.trans _ physicalBase_zero.symm
  rw [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hz,hsecond] with x hzx hsx
  intro hx
  by_cases hx1 : x ≤ 1
  · exact hzx ⟨hx.1,hx1⟩
  · have hm : x + -1 ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hx.2]
    simpa only [neg_add_cancel_right,Pi.zero_apply] using hsx hm

/-- Subtraction is respected by the physical coefficient representative almost everywhere. -/
theorem physicalBase_sub (a b : PairSpace 2) :
    physicalBase (a-b) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => physicalBase a x-physicalBase b x) := by
  have h₁ := circle_ae_pullback (Lp.coeFn_sub (l2Synthesis a.1) (l2Synthesis b.1))
  have h₂ := circle_ae_pullback (Lp.coeFn_sub (l2Synthesis a.2) (l2Synthesis b.2))
  filter_upwards [h₁,h₂] with x hx hy
  change (circlePullback (l2Synthesis (a.1-b.1)) x,circlePullback (l2Synthesis (a.2-b.2)) x) = _
  rw [map_sub,map_sub]
  exact Prod.ext hx hy

/-- For an even potential, an original parity eigen-equation can be checked on the unit interval. -/
theorem operator_eq_smul_of_physical_unit_parity (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (a : Domain 2) (r : ℤ) (ha : a ∈ domainParitySubspace r)
    (z : ℂ) (he : physicalOperator (physicalBase φ) (physicalDomain a)
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • physicalDomain a x)) :
    operator (by simp) φ a = z • domainInclusion a := by
  apply sub_eq_zero.mp
  apply pairParity_eq_zero_of_physicalBase_unit _ r
    ((pairParitySubspace r).sub_mem (operator_mem_pairParitySubspace (by simp) φ hφ r a ha)
      ((pairParitySubspace r).smul_mem z ((mem_domainParitySubspace r a).mp ha)))
  have hs := physicalBase_sub (operator (by simp) φ a) (z • domainInclusion a)
  have ho := physical_operator_realization φ a
  have hm := physicalBase_smul z (domainInclusion a)
  have hi := physicalBase_domainInclusion a
  have hfull : physicalBase (operator (by simp) φ a-z • domainInclusion a)
      =ᵐ[volume.restrict (Ioc 0 2)] (fun x =>
        physicalOperator (physicalBase φ) (physicalDomain a) x-z • physicalDomain a x) := by
    filter_upwards [hs,ho,hm,hi] with x hsx hox hmx hix
    rw [hsx,hox,hmx,hix]
  have hunit := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) hfull
  filter_upwards [hunit,he] with x hx hex
  simp only [hx,hex,sub_self,Pi.zero_apply]

end NLS.ZakharovShabat
