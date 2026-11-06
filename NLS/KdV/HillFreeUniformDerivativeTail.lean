import NLS.SequenceSpaces.UniformOperatorOutputTails
import NLS.KdV.HillFreePeriodCompactRemainder
import NLS.KdV.HillFreeUniformDiagonalTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual free derivative remainder after its original diagonal
correction is removed. -/
def hillFreePeriodOffDiagonalRemainder (n : ℕ) (hn : 1≤n) (a : Coeff 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+
    Coeff.positiveDeletedProjection 2 (n : ℤ)+
      Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a)

theorem norm_hillFreePeriodOffDiagonalRemainder_coordinate_le
    (n : ℕ) (hn : 1≤n) (a h : Coeff 2) (m : ℤ) :
    ‖hillFreePeriodOffDiagonalRemainder hq hr n hn a h m‖≤
      (2*Real.exp ((2/Real.pi^2)*(‖a‖+2)))*‖a m‖*‖h‖ := by
  let D := Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a)
  let C := 2*Real.exp ((2/Real.pi^2)*(‖a‖+2))
  let b : Coeff 2 := (C : ℂ) • a
  have hrow : ‖hillFreePeriodOffDiagonalRemainder hq hr n hn a h m‖≤‖b m‖*‖h‖ := by
    change ‖(fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a h+
        Coeff.positiveDeletedProjection 2 (n : ℤ) h+D h) m‖ ≤ ‖b m‖*‖h‖
    simp only [lp.coeFn_add,Pi.add_apply]
    rw [fderiv_hillFreeScaledPeriodSequence_coordinate hq hr n hn,
      Coeff.positiveDeletedProjection_apply]
    have hD : D h m = (if 0 < m ∧ m ≠ (n : ℤ) then
        hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1 else 0)*h m := rfl
    rw [hD]
    by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
    · rw [if_pos hm,if_pos hm,if_pos hm]
      have he : -h m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-
          a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h+
          h m+(hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1)*h m =
          -(a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h) := by ring
      rw [he,norm_neg,norm_mul]
      have hnorm : ‖fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h‖ ≤ C*‖h‖ :=
        ((fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a).le_opNorm h).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_hilbertWeightedProduct_hillSeparated_le n m.toNat a) (norm_nonneg h))
      have hb : ‖b m‖ = C*‖a m‖ := by
        simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ C by dsimp [C];positivity)]
      rw [hb]
      nlinarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg (a m))]
    · rw [if_neg hm,if_neg hm,if_neg hm,zero_mul,zero_add,add_zero,norm_zero]
      positivity

  have hb : ‖b m‖=C*‖a m‖ := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (show 0≤C by dsimp only [C];positivity)]
  simpa only [hb] using hrow

theorem exists_hillFreePeriodOffDiagonalRemainder_uniform_outputTail
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t → ∀ n : ℕ, ∀ hn : 1≤n, ∀ a∈K,
      ‖hillFreePeriodOffDiagonalRemainder hq hr n hn a-
        (Coeff.truncateCLM t).comp (hillFreePeriodOffDiagonalRemainder hq hr n hn a)‖<ε := by
  let b : Coeff 2 → Coeff 2 := fun a =>
    ((2*Real.exp ((2/Real.pi^2)*(‖a‖+2)) : ℝ) : ℂ) • a
  have hb : Continuous b := by fun_prop
  let ι := {v : ℕ × Coeff 2 // 1≤v.1 ∧ v.2∈K}
  let T : ι → Coeff 2 →L[ℂ] Coeff 2 := fun i =>
    hillFreePeriodOffDiagonalRemainder hq hr i.val.1 i.property.1 i.val.2
  have hrow : ∀ i : ι, ∀ m : ℤ, m∉(∅ : Finset ℤ) → ∀ h : Coeff 2,
      ‖T i h m‖≤‖b i.val.2 m‖*‖h‖ := by
    intro i m _ h
    simpa only [b,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (show 0<2*Real.exp ((2/Real.pi^2)*(‖i.val.2‖+2)) by positivity)] using
      norm_hillFreePeriodOffDiagonalRemainder_coordinate_le hq hr i.val.1 i.property.1 i.val.2 h m
  obtain ⟨s,_,hs⟩ := Coeff.exists_uniform_outputTail_operator_of_compact_rowMajorants
    (by norm_num : (2 : ℝ≥0∞)≠⊤) T (fun i => b i.val.2) (b '' K) (hK.image hb)
    (fun i => ⟨i.val.2,i.property.2,rfl⟩) ∅ hrow ε hε
  refine ⟨s,?_⟩
  intro t hst n hn a ha
  exact hs t hst ⟨(n,a),hn,ha⟩

/-- The entire actual free root derivative remainder has uniformly
small output tails on compact root sets, uniformly in the omitted index. -/
theorem exists_fderiv_hillFreeScaledPeriodSequence_add_projection_uniform_outputTail
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t → ∀ n : ℕ, ∀ hn : 1≤n, ∀ a∈K,
      ‖(fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+Coeff.positiveDeletedProjection 2 (n : ℤ))-
        (Coeff.truncateCLM t).comp (fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+
          Coeff.positiveDeletedProjection 2 (n : ℤ))‖<ε := by
  obtain ⟨s,hs⟩ := exists_hillFreePeriodOffDiagonalRemainder_uniform_outputTail hq hr K hK (ε/2) (by positivity)
  obtain ⟨J,hJ⟩ := exists_hillFreePeriodDiagonalCorrection_uniform_operator_tail_bound K hK (ε/2) (by positivity)
  refine ⟨s∪Coeff.lowFrequencies J,?_⟩
  intro t hst n hn a ha
  let R := fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+Coeff.positiveDeletedProjection 2 (n : ℤ)
  let D := Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a)
  let P := Coeff.truncateCLM (p := 2) t
  have hfirst : ‖(R+D)-P.comp (R+D)‖<ε/2 :=
    hs t (Finset.Subset.trans Finset.subset_union_left hst) n hn a ha
  have hdiag0 : ‖D-(Coeff.truncateCLM (Coeff.lowFrequencies J)).comp D‖≤ε/2 := by
    simpa only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp] using hJ n a ha
  have hdiag : ‖D-P.comp D‖≤ε/2 :=
    (Coeff.norm_outputTail_operator_mono D (Coeff.lowFrequencies J) t
      (Finset.Subset.trans Finset.subset_union_right hst)).trans hdiag0
  have he : R-P.comp R=((R+D)-P.comp (R+D))-(D-P.comp D) := by
    have hadd : P.comp (R+D)=P.comp R+P.comp D := by
      ext x
      simp only [ContinuousLinearMap.comp_apply,add_apply,map_add]
    rw [hadd]
    abel
  change ‖R-P.comp R‖<ε
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end NLS.KdV
