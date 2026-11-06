import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.CompactHolderDerivative

/-! # Uniform nonlinear compactness for the actual distributional Miura map

Bounded convolution families have a fixed inverse-bracket majorant in
HminusOne. This controls the entire nonlinear correction on bounded L2
sets, rather than only each of its linearized derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem isCompactOperator_boundedCoefficientsHminusOne :
    IsCompactOperator boundedCoefficientsHminusOne := by
  have he : Coeff.holderProduct (p := 2) (r := ⊤) (q := 2) inverseBracketCoefficients =
      (Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).flip inverseBracketCoefficients := by
    ext b j
    change inverseBracketCoefficients j*b j = b j*inverseBracketCoefficients j
    exact mul_comm _ _
  unfold boundedCoefficientsHminusOne
  rw [he]
  exact (Coeff.isCompactOperator_holderProduct_fixed_right (by norm_num) inverseBracketCoefficients).clm_comp
    (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem isCompactOperator_periodOneL2Inclusion : IsCompactOperator periodOneL2Inclusion :=
  isCompactOperator_boundedCoefficientsHminusOne.comp_clm _

/-- ONE compact set contains ALL actual products of two bounded L2
families, with no finite support, reality or smallness assumption. -/
theorem exists_compact_periodOneMiuraProducts (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B) :
    ∃ K : Set PeriodOneHminusOne, IsCompact K ∧
      ∀ a b : Coeff 2, ‖a‖ ≤ A → ‖b‖ ≤ B → periodOneMiuraProduct a b ∈ K := by
  let K := closure (boundedCoefficientsHminusOne '' closedBall (0 : Coeff ⊤) (A*B))
  refine ⟨K,isCompactOperator_boundedCoefficientsHminusOne.isCompact_closure_image_of_bounded
    isBounded_closedBall,?_⟩
  intro a b ha hb
  apply subset_closure
  refine ⟨Coeff.youngConvolution youngRelation_two_two_top a b,?_,rfl⟩
  rw [mem_closedBall_zero_iff]
  exact (Coeff.norm_youngConvolution_le youngRelation_two_two_top a b).trans
    (mul_le_mul ha hb (norm_nonneg b) hA)

def periodOneMiuraCorrection (a : Coeff 2) : PeriodOneHminusOne :=
  periodOneMiuraProduct a a-periodOneL2Inclusion a

theorem periodOneMiura_eq_mass_add_correction (a : Coeff 2) :
    periodOneMiura a = periodOneMassOperator 0 a+periodOneMiuraCorrection a := by
  unfold periodOneMiura periodOneShiftedMiura periodOneMiuraCorrection
  abel

/-- The full actual nonlinear correction maps EVERY bounded L2 set
into a norm-precompact subset of the genuine HminusOne space. -/
theorem isCompact_closure_periodOneMiuraCorrection_image_of_bounded
    {S : Set (Coeff 2)} (hS : Bornology.IsBounded S) :
    IsCompact (closure (periodOneMiuraCorrection '' S)) := by
  obtain ⟨A,hA⟩ := hS.exists_norm_le
  let B := max A 0
  obtain ⟨K,hK,hproducts⟩ := exists_compact_periodOneMiuraProducts B B (le_max_right _ _) (le_max_right _ _)
  have hL := isCompactOperator_periodOneL2Inclusion.isCompact_closure_image_of_bounded hS
  have hKL := (hK.prod hL).image (continuous_fst.sub continuous_snd)
  apply hKL.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨(periodOneMiuraProduct a a,periodOneL2Inclusion a),
      ⟨hproducts a a ((hA a ha).trans (le_max_left _ _))
        ((hA a ha).trans (le_max_left _ _)),subset_closure ⟨a,ha,rfl⟩⟩,rfl⟩
  · exact hKL.isClosed

/-- Convergent actual Miura images of a bounded COMPLEX L2 sequence
have a strongly L2 convergent subsequence with exactly that Miura image. -/
theorem exists_periodOneMiura_tendsto_subseq_of_bounded
    (a : ℕ → Coeff 2) (hb : Bornology.IsBounded (range a))
    (q : PeriodOneHminusOne) (hq : Tendsto (fun n => periodOneMiura (a n)) atTop (𝓝 q)) :
    ∃ b : Coeff 2, periodOneMiura b = q ∧ ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) := by
  have hK := isCompact_closure_periodOneMiuraCorrection_image_of_bounded hb
  obtain ⟨c,_hc,σ,hσ,hc⟩ := hK.tendsto_subseq
    (fun n => subset_closure ⟨a n,⟨n,rfl⟩,rfl⟩)
  let b := periodOneMassInverse 0 (q-c)
  have he (u : Coeff 2) : periodOneMassInverse 0 (periodOneMiura u-periodOneMiuraCorrection u) = u := by
    rw [periodOneMiura_eq_mass_add_correction,add_sub_cancel_right,periodOneMassInverse_operator]
  have ht : Tendsto (a ∘ σ) atTop (𝓝 b) := by
    have h := (periodOneMassInverse 0).continuous.continuousAt.tendsto.comp
      ((hq.comp hσ.tendsto_atTop).sub hc)
    simpa only [Function.comp_def,he,b] using h
  have hcont : Continuous periodOneMiura :=
    (continuous_iff_continuousAt.mpr fun u => (analyticAt_periodOneShiftedMiura 0 u).continuousAt).sub
      periodOneL2Inclusion.continuous
  exact ⟨b,tendsto_nhds_unique (hcont.continuousAt.tendsto.comp ht) (hq.comp hσ.tendsto_atTop),σ,hσ,ht⟩

end NLS
