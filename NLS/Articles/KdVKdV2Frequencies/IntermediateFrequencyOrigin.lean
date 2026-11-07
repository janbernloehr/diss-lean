import NLS.Articles.KdVKdV2Frequencies.IntermediateHilbertActionRays
import NLS.Articles.KdVKdV2Frequencies.GlobalScalarHilbertFrequencyAgreement
import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedWeakFrequencyCompatibility
import NLS.Articles.KdVConvexity.NormalizedPhysicalTaylor
import NLS.SequenceSpaces.WeightedRayZeroDerivative

/-! The ACTUAL global intermediate frequency has the full original
normalization F(0)=0 and dF(0)=-6Id at EVERY intermediate order.
Finite coordinate rays retain the literal original action weights. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem intermediate_frequency_origin_normalization
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (α : ℝ) (hα0 : -1<α) (hα1 : α<0)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D (-α) ((α+1)/2)) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    weakActionEnumeration (F 0)=0 ∧
      fderiv ℂ (fun b => weakActionEnumeration (F b)) 0=
        (-6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1) := by
  have hrays (i j : ℤ) (t : ℝ) (ht : 0≤t) :
      weakActionEnumeration (F ((t : ℂ) • lp.single 1 j 1)) i=
        (Weight.sobolev α (actionIndexEquiv i : ℤ) : ℂ)*
          normalizedActionGradient E.hamiltonian
            (((t : ℂ)/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ)) • lp.single 2 j 1) i := by
    have hfreq := negativeWeighted_packet_agrees_actual_weak_frequency D (-α) ((α+1)/2)
      (by linarith) (by linarith) (by linarith) (by ring) U F hU hCU hF hpair V G hV hCV hG hrec
        ((t : ℂ) • lp.single 1 j 1) (nonnegative_real_single_ray 1 j t ht) (actionIndexEquiv i)
    simp only [neg_neg] at hfreq
    rw [weakActionEnumeration_apply,hfreq,normalized_weak_single_ray_hilbert]
    have hapos : actionUnreindex
        (((t : ℂ)/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ)) • lp.single 2 j 1)∈positiveQuadrant :=
      fun n => intermediate_hilbert_single_ray_nonnegative α j t ht (actionIndexEquiv.symm n)
    rw [global_scalar_frequency_eq_physical_hilbert_gradient D E V G hV hCV hG
      (global_physical_family_native_recovery D G hrec) _ hapos]
    rfl
  constructor
  · ext i
    have h := hrays i i 0 le_rfl
    simpa only [Complex.ofReal_zero,zero_smul,zero_div,E.normalized_gradient_Taylor.1,
      lp.coeFn_zero,Pi.zero_apply,mul_zero] using h
  · have hf0 : AnalyticAt ℂ (fun b => weakActionEnumeration (F b)) 0 :=
      (weakActionEnumeration.analyticAt _).comp (hF 0 (hCU (Coeff.zero_mem_nonnegativeLocus 1)))
    have hg0 : AnalyticAt ℂ (normalizedActionGradient E.hamiltonian) 0 :=
      analyticOnNhd_normalizedActionGradient E.hamiltonian E.domain E.analytic 0
        (by rw [mem_preimage,map_zero];exact E.contains_cone zero_mem_positiveQuadrant)
    exact Coeff.fderiv_zero_of_weighted_ray_agreement _ _ hf0 hg0
      (fun i => (Weight.sobolev α (actionIndexEquiv i : ℤ) : ℂ))
      (fun i => Weight.complex_ne_zero _ _) (-6) E.normalized_gradient_Taylor.2 hrays

end NLS.Articles.KdVKdV2Frequencies
