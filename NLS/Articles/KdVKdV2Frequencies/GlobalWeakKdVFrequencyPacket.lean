import NLS.Articles.KdVKdV2Frequencies.GlobalBoundedFrequencyActionCharts
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.KdV.ClassicalPeriodOperator

/-! A genuine Banach-valued weighted frequency extension on ONE complex
neighborhood of the ENTIRE nonnegative weak-action cone, with exact native
Hamiltonian recovery at every source. The target here is weighted infinity;
the sharper finite-p remainder and compactness assertions remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_global_actual_weak_kdv_frequency_packet (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ g : Coeff 1 → Coeff ⊤,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ AnalyticOnNhd ℂ g V ∧
      (∀ a∈V, ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (g a j).im=0) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
          ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨U,G,hU,hcone,hG,hbound,hrec⟩ := exists_global_locally_bounded_physical_frequency_corrections D
  let V := weakActionEnumeration ⁻¹' U
  have hV : IsOpen V := hU.preimage weakActionEnumeration.continuous
  have hconeV : Coeff.nonnegativeLocus 1⊆V := fun a ha => hcone (weakActionEnumeration_nonnegative a ha)
  let f : Coeff 1 → ℤ → ℂ := fun a j => if hj : 0<j then
    G (positiveIntegerIndex j hj) (weakActionEnumeration a)/(positiveIntegerIndex j hj : ℂ) else 0
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun a => f a j) V := by
    by_cases hj : 0<j
    · intro a ha
      have hh : AnalyticAt ℂ
          (fun b => G (positiveIntegerIndex j hj) (weakActionEnumeration b)/(positiveIntegerIndex j hj : ℂ)) a :=
        ((hG (positiveIntegerIndex j hj) _ ha).comp (weakActionEnumeration.analyticAt a)).div_const
      exact hh.congr (Eventually.of_forall (fun _ => by simp only [f,dif_pos hj]))
    · simpa only [f,dif_neg hj] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Coeff 1 => (0 : ℂ)) V)
  have hlocal (a : Coeff 1) (ha : a∈V) :
      ∃ W : Set (Coeff 1), IsOpen W ∧ a∈W ∧ W⊆V ∧
        ∃ K : ℝ, ∀ b∈W, ∃ v : Coeff ⊤, (∀ j, v j=f b j) ∧ ‖v‖≤K := by
    obtain ⟨T,hT,haT,hTU,K,hK,hTb⟩ := hbound _ ha
    refine ⟨weakActionEnumeration ⁻¹' T,hT.preimage weakActionEnumeration.continuous,haT,
      (fun b hb => hTU hb),K,?_⟩
    intro b hb
    have hc (j : ℤ) : ‖f b j‖≤K := by
      dsimp only [f]
      split_ifs
      · exact hTb _ hb _
      · simpa only [norm_zero] using hK.le
    let v : Coeff ⊤ := ⟨f b,memℓp_infty ⟨K,by rintro _ ⟨j,rfl⟩;exact hc j⟩⟩
    refine ⟨v,(fun _ => rfl),?_⟩
    exact lp.norm_le_of_forall_le hK.le hc
  obtain ⟨hgcoeff,hga⟩ := Coeff.analytic_realization_of_local_bounds (r := ⊤) f hV hcoord hlocal
  let g := fun a => Coeff.ofFunctionOrZero ⊤ (f a)
  have hpos (a : Coeff 1) (ha : a∈V) (n : ℕ+) :
      g a (n : ℤ)=G n (weakActionEnumeration a)/(n : ℂ) := by
    rw [hgcoeff a ha]
    have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
    rw [show f a (n : ℤ)=_ from dif_pos hn]
    have he : positiveIntegerIndex (n : ℤ) hn=n := by apply Subtype.ext; simp only [positiveIntegerIndex,Int.toNat_natCast];rfl
    rw [he]
  have hzero (a : Coeff 1) (ha : a∈V) (j : ℤ) (hj : j≤0) : g a j=0 := by
    rw [hgcoeff a ha]
    exact dif_neg (by omega)
  refine ⟨V,g,hV,hconeV,hga,hzero,?_,?_⟩
  · intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      rw [←hnj,hpos a (hconeV ha) n]
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_physical_pair_of_nonnegative_actions D (weakActionEnumeration a)
        (weakActionEnumeration_nonnegative a ha)
      rw [←hQ,hrec P z hz hzr n]
      have hr : (P.correction n z).im=0 := physicalMiuraFrequencyChart_real D P.source_chart (P.potential z)
        (P.real_potential z hz hzr) (P.mean_zero z hz) (P.source_mem z hz) n
      simp only [div_im,Complex.natCast_re,Complex.natCast_im,hr,mul_zero,zero_mul,sub_zero,zero_div]
    · rw [hzero a (hconeV ha) j (by omega)];rfl
  · intro q n
    have ha : D.nativeWeakActionSequence 1 q∈Coeff.nonnegativeLocus 1 :=
      Coeff.quadraticActions_mem_nonnegativeLocus _ (Coeff.signedToCartesian_real (D.nativeWeakSignedTarget 1 q))
    rw [hpos _ (hconeV ha) n,global_physical_family_native_recovery D G hrec q n]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
