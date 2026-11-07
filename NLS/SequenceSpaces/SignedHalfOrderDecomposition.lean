import NLS.SequenceSpaces.SignedHalfOrderTarget

/-! The exact normalized positive-packet decomposition gives the SAME
signed raw target, with h^(1/2) core and h^(3/2) remainder. -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

theorem exists_signed_half_packet_decomposition (v : Weight) (hv : ∀ j, v (-j)=v j)
    (U : Set (WeightedCoeff v 2)) (hU : IsOpen U) (q : WeightedCoeff v 2) (hq : q∈U)
    (hJq : conjugateReflection v hv q=q) (e : ℤ → Bool) (G : WeightedCoeff v 2 → Coeff 2)
    (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev 1) 2)
    (R : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev 2) 2)
    (CA CR : ℝ) (hAa : AnalyticOnNhd ℂ A U) (hRa : AnalyticOnNhd ℂ R U)
    (hAb : ∀ p∈U, ‖A p‖≤CA) (hRb : ∀ p∈U, ‖R p‖≤CR)
    (hG : ∀ p∈U, ∀ j : ℤ, G p j=if e j then -((A p).val j+(R p).val j) else (A p).val j+(R p).val j) :
    ∃ V : Set (WeightedCoeff v 2), IsOpen V ∧ q∈V ∧ V⊆U ∧
      (∀ p∈V, conjugateReflection v hv p∈U) ∧
      AnalyticOnNhd ℂ (signedHalfTarget v 1 e A) V ∧ AnalyticOnNhd ℂ (signedHalfTarget v 2 e R) V ∧
      ∀ p∈V, ‖signedHalfTarget v 1 e A p‖≤2*CA ∧ ‖signedHalfTarget v 2 e R p‖≤2*CR ∧
        signedTargetLift v (Weight.sobolev (-1/2)) G p=
          sobolevInclusion (by norm_num : (-1/2:ℝ)≤1-1/2) (signedHalfTarget v 1 e A p)+
          sobolevInclusion (by norm_num : (-1/2:ℝ)≤2-1/2) (signedHalfTarget v 2 e R p) := by
  let V := U∩conjugateReflection v hv ⁻¹' U
  have hV : IsOpen V := hU.inter (hU.preimage (continuous_conjugateReflection v hv))
  refine ⟨V,hV,⟨hq,by change conjugateReflection v hv q∈U; rw [hJq]; exact hq⟩,inter_subset_left,(fun p hp => hp.2),
    analyticOnNhd_signedHalfTarget v hv 1 e A U hAa,analyticOnNhd_signedHalfTarget v hv 2 e R U hRa,?_⟩
  intro p hp
  refine ⟨norm_signedHalfTarget_le v hv 1 e A p CA (hAb p hp.1) (hAb _ hp.2),
    norm_signedHalfTarget_le v hv 2 e R p CR (hRb p hp.1) (hRb _ hp.2),?_⟩
  have hg (z) (hz : z∈U) (j : ℤ) : G z j=
      (if e j then -(A z).val j else (A z).val j)+(if e j then -(R z).val j else (R z).val j) := by
    rw [hG z hz j]
    cases e j <;> simp only [Bool.false_eq_true,↓reduceIte]
    ring
  apply Subtype.ext
  funext j
  rw [signedTargetLift_apply,normalizedSignedCompletion_apply v hv,WeightedCoeff.add_val,
    sobolevInclusion_apply,sobolevInclusion_apply,signedHalfTarget_apply v hv,signedHalfTarget_apply v hv,
    hg p hp.1 j,hg _ hp.2 (-j),map_add]
  have hw : (Weight.sobolev (1/2) j:ℂ)*(Weight.sobolev (-1/2) j:ℂ)=1 := by
    rw [←Complex.ofReal_mul,←Weight.sobolev_add,show (1/2:ℝ)+(-1/2)=0 by ring,
      Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one]
  apply (div_eq_iff (Weight.complex_ne_zero _ _)).mpr
  linear_combination (norm := ring)
    -((if e j then -(A p).val j else (A p).val j)+(if e j then -(R p).val j else (R p).val j)+
      conj (if e (-j) then -(A (conjugateReflection v hv p)).val (-j) else (A (conjugateReflection v hv p)).val (-j))+
      conj (if e (-j) then -(R (conjugateReflection v hv p)).val (-j) else (R (conjugateReflection v hv p)).val (-j)))*hw

end NLS.WeightedCoeff
