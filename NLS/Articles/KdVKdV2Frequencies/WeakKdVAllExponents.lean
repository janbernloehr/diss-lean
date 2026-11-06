import NLS.Articles.KdVKdV2Frequencies.GlobalWeakLpKdVFrequencyPacket
import NLS.SequenceSpaces.PositiveIndexWeakLift

/-! The s=-1 target clause of Theorem1.2(i): ONE actual frequency map on
the entire nonnegative normalized weak cone has values in EVERY original
weighted ell(-1,r), r>1, with genuine Banach-analytic extensions. All targets
retain the SAME raw physical corrections and positive action normalization. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_weak_kdv_frequency_all_exponents (D : GlobalRoughAbelianForwardData) :
    ∃ ω : Coeff 1 → ℤ → ℂ,
      (∀ a : Coeff 1, ∀ j : ℤ, j≤0 → ω a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (ω a j).im=0) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        ω (D.nativeWeakActionSequence 1 q) (n : ℤ)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ r : ℝ≥0∞, ∀ hr : 1<r, letI : Fact (1 ≤ r) := ⟨hr.le⟩;
        ∃ U : Set (Coeff 1), ∃ F : Coeff 1 → WeightedCoeff (Weight.sobolev (-1)) r,
          IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ F U ∧
          (∀ a : Coeff 1, ∀ j : ℤ, j≤0 → (F a).val j=0) ∧
          ∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (F a).val j=ω a j := by
  obtain ⟨U₀,G₀,_hU₀,_hcone₀,_hG₀,hrec₀⟩ := exists_global_physical_frequency_action_corrections D
  let ω := fun (a : Coeff 1) (j : ℤ) => if hj : 0<j then
    G₀ (positiveIntegerIndex j hj) (weakActionEnumeration a) else 0
  have hzero (a : Coeff 1) (j : ℤ) (hj : j≤0) : ω a j=0 := dif_neg (by omega)
  have hpos (a : Coeff 1) (n : ℕ+) : ω a (n : ℤ)=G₀ n (weakActionEnumeration a) := by
    have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
    change (if hj : (0 : ℤ)<n then G₀ (positiveIntegerIndex (n : ℤ) hj) (weakActionEnumeration a) else 0)=_
    rw [dif_pos hn]
    have he : positiveIntegerIndex (n : ℤ) hn=n := by
      apply Subtype.ext
      simp only [positiveIntegerIndex,Int.toNat_natCast]
      rfl
    rw [he]
  refine ⟨ω,hzero,?_,?_,?_⟩
  · intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_physical_pair_of_nonnegative_actions D (weakActionEnumeration a)
        (weakActionEnumeration_nonnegative a ha)
      rw [←hnj,hpos,←hQ,hrec₀ P z hz hzr n]
      exact physicalMiuraFrequencyChart_real D P.source_chart (P.potential z)
        (P.real_potential z hz hzr) (P.mean_zero z hz) (P.source_mem z hz) n
    · rw [hzero a j (by omega)];rfl
  · intro q n
    rw [hpos]
    exact global_physical_family_native_recovery D G₀ hrec₀ q n
  · intro r hr
    let : Fact (1 ≤ r) := ⟨hr.le⟩
    obtain ⟨V,G,hV,hcone,hG,_hGzero,hrec⟩ := exists_global_physical_lp_action_packet D hr
    let U := weakActionEnumeration ⁻¹' V
    let F := fun a => Coeff.positiveIndexWeakLift (G (weakActionEnumeration a))
    have hFa : AnalyticOnNhd ℂ F U := by
      intro a ha
      exact (Coeff.positiveIndexWeakLift.analyticAt _).comp ((hG _ ha).comp (weakActionEnumeration.analyticAt a))
    refine ⟨U,F,hV.preimage weakActionEnumeration.continuous,
      (fun a ha => hcone (weakActionEnumeration_nonnegative a ha)),hFa,
      (fun a j hj => Coeff.positiveIndexWeakLift_nonpositive _ j hj),?_⟩
    intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_physical_pair_of_nonnegative_actions D (weakActionEnumeration a)
        (weakActionEnumeration_nonnegative a ha)
      change (Coeff.positiveIndexWeakLift (G (weakActionEnumeration a))).val j=ω a j
      rw [←hnj,Coeff.positiveIndexWeakLift_positive,hpos,←hQ,hrec₀ P z hz hzr n,
        lp_packet_recovers_all_physical_pairs D hr G hrec P z hz hzr n]
      have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
      field_simp
    · rw [Coeff.positiveIndexWeakLift_nonpositive _ j (by omega),hzero a j (by omega)]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
