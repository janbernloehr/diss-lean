import NLS.Articles.KdVKdV2Frequencies.GlobalWeakKdVFrequencyPacket
import NLS.Articles.KdVKdV2Frequencies.ActualHilbertWeakFrequencyAgreement

/-! The SAME global actual weak-frequency packet and physical Hilbert
 gradient agree on one full complex Hilbert neighborhood of the ENTIRE
 nonnegative Hilbert cone. The cone lies in one common connected component,
 so the physically calibrated origin germ continues before ALL indices. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

theorem hilbert_positiveQuadrant_convex : Convex ℝ positiveQuadrant := by
  intro a ha b hb u v hu hv _ n
  change (u • a n+v • b n).im=0 ∧ 0≤(u • a n+v • b n).re
  constructor
  · simp [(ha n).1,(hb n).1]
  · simpa using add_nonneg (mul_nonneg hu (ha n).2) (mul_nonneg hv (hb n).2)

theorem exists_packet_hilbert_domain (D : GlobalRoughAbelianForwardData)
    (U : Set (Coeff 1)) (g : Coeff 1 → Coeff ⊤) (hU : IsOpen U)
    (hcone : Coeff.nonnegativeLocus 1⊆U) (hg : AnalyticOnNhd ℂ g U)
    (hrec : ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
      g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
        ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ))
    (E : PhysicalHstarExtension) :
    ∃ V : Set ActionSpace, IsOpen V ∧ positiveQuadrant⊆V ∧ V⊆E.domain ∧
      (∀ a∈V, hilbertWeakActions a∈U) ∧
      ∀ a∈V, ∀ n : ℕ+, g (hilbertWeakActions a) (n : ℤ)=actionGradient E.hamiltonian a n/(n : ℂ) := by
  let W := E.domain∩hilbertWeakActions ⁻¹' U
  have hW : IsOpen W := E.isOpen.inter (hU.preimage hilbertWeakActions.continuous)
  have hCW : positiveQuadrant⊆W := fun a ha =>
    ⟨E.contains_cone ha,hcone (hilbertWeakActions_nonnegative a ha)⟩
  let V := connectedComponentIn W (0 : ActionSpace)
  have hV : IsOpen V := hW.connectedComponentIn
  have hCV : positiveQuadrant⊆V := hilbert_positiveQuadrant_convex.isPreconnected.subset_connectedComponentIn
    zero_mem_positiveQuadrant hCW
  have hVW : V⊆W := connectedComponentIn_subset W 0
  have h0V : (0 : ActionSpace)∈V := mem_connectedComponentIn (hCW zero_mem_positiveQuadrant)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU 0 (hcone (by intro j;simp))
  let f : ℕ+ → Coeff 1 → ℂ := fun n a => (n : ℂ)*g a (n : ℤ)
  have hf (n : ℕ+) : AnalyticOnNhd ℂ (f n) U := by
    intro a ha
    exact analyticAt_const.mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n : ℤ)).analyticAt _).comp (hg a ha))
  have hfrecover (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
      (_hq : D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) r) (n : ℕ+) :
      f n (D.nativeWeakActionSequence 1 q)=
        (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
    change (n : ℂ)*g (D.nativeWeakActionSequence 1 q) (n : ℤ)=_
    rw [hrec q n]
    have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
    field_simp
  refine ⟨V,hV,hCV,(fun a ha => (hVW ha).1),(fun a ha => (hVW ha).2),?_⟩
  intro a ha n
  have hfa : AnalyticOnNhd ℂ (fun b : ActionSpace => f n (hilbertWeakActions b)) V :=
    fun b hb => (hf n _ (hVW hb).2).comp (hilbertWeakActions.analyticAt b)
  have hG : AnalyticOnNhd ℂ (fun b : ActionSpace => actionGradient E.hamiltonian b n) V :=
    fun b hb => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
      (analyticOnNhd_actionGradient _ E.analytic b (hVW hb).1)
  have he := hfa.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_connectedComponentIn h0V
    (D.weakFrequency_eventuallyEq_HilbertGradient_zero E r hr f (fun n => (hf n).mono hball) hfrecover n) ha
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
  exact (eq_div_iff hn).mpr ((mul_comm _ _).trans he)

namespace GlobalRoughAbelianForwardData

theorem exists_global_actual_hilbert_weak_kdv_frequency (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (Coeff 1), ∃ g : Coeff 1 → Coeff ⊤,
      ∃ E : PhysicalHstarExtension, ∃ V : Set ActionSpace,
      IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ a∈U, ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (g a j).im=0) ∧
      IsOpen V ∧ positiveQuadrant⊆V ∧ V⊆E.domain ∧
      (∀ a∈V, hilbertWeakActions a∈U) ∧
      AnalyticOnNhd ℂ (actionGradient E.hamiltonian) V ∧
      (∀ a∈V, ∀ n : ℕ+, g (hilbertWeakActions a) (n : ℤ)=actionGradient E.hamiltonian a n/(n : ℂ)) ∧
      actionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (actionGradient E.hamiltonian) 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
          ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨U,g,hU,hcone,hg,hzero,hreal,hrec⟩ := D.exists_global_actual_weak_kdv_frequency_packet
  let E := Classical.choice nonempty_physicalHstarExtension
  obtain ⟨V,hV,hpos,hVE,hweak,heq⟩ := exists_packet_hilbert_domain D U g hU hcone hg hrec E
  have ht := E.Taylor_at_zero
  exact ⟨U,g,E,V,hU,hcone,hg,hzero,hreal,hV,hpos,hVE,hweak,
    (analyticOnNhd_actionGradient _ E.analytic).mono hVE,heq,ht.2.1,ht.2.2,hrec⟩

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
