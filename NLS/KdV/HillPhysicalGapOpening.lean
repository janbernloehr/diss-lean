import NLS.KdV.HillPhysicalGapGermNontrivial
import NLS.KdV.HillLocalGapPhysicalMatching
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Every selected physical gap opens near every real L2 potential

The squared gap is real analytic along every affine physical line.
Uniqueness on that line propagates a hypothetical collapsed germ to a
potential whose selected gap is open, contradicting the free derivative.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

def hillPhysicalRealLine (p v : RealPeriodOneHillPotential) (t : ℝ) :
    RealPeriodOneHillPotential :=
  ⟨p.val+(t : ℂ) • (v.val-p.val),by
    constructor
    · rw [map_add,map_smul,map_sub]
      exact (Coeff.paritySubspace 0).add_mem p.property.1
        ((Coeff.paritySubspace 0).smul_mem _
          ((Coeff.paritySubspace 0).sub_mem v.property.1 p.property.1))
    · intro k
      simp only [map_add,map_smul,map_sub,lp.coeFn_add,lp.coeFn_smul,lp.coeFn_sub,
        Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Complex.conj_ofReal,
        p.property.2 k,v.property.2 k,map_mul]⟩

theorem continuous_hillPhysicalRealLine (p v : RealPeriodOneHillPotential) :
    Continuous (hillPhysicalRealLine p v) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

theorem analyticAt_hillRealGapSquare_realLine (p v : RealPeriodOneHillPotential)
    (n : ℕ+) (t : ℝ) :
    AnalyticAt ℝ (fun s => (2*(hillRealGapHalfLength (hillPhysicalRealLine p v s).val
      (hillPhysicalRealLine p v s).property.1 (hillPhysicalRealLine p v s).property.2
      (n : ℕ) : ℂ))^2) t := by
  let q := hillPhysicalRealLine p v t
  let P : ℝ → Coeff 2 := fun s => SpectralWeight.one.toCoeff (hillPhysicalRealLine p v s).val
  let L : ℝ →L[ℝ] Coeff 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight
    (SpectralWeight.one.toCoeff v.val-SpectralWeight.one.toCoeff p.val)
  have hP : AnalyticAt ℝ P t := by
    have he : P = fun s => SpectralWeight.one.toCoeff p.val+L s := by
      funext s
      simp only [P,hillPhysicalRealLine,map_add,map_smul,map_sub]
      rfl
    rw [he]
    exact analyticAt_const.add (L.analyticAt t)
  obtain ⟨A,_,hqA,_,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood
    q.val q.property.1 q.property.2 (n : ℕ) n.property
  have hlocal := ((hS _ hqA).restrictScalars (𝕜 := ℝ)).comp (f := P) hP
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood
    q.val q.property.1 q.property.2 (n : ℕ) n.property
  have he := ((continuous_hillPhysicalRealLine p v).tendsto t).eventually (hW.mem_nhds hqW)
  apply hlocal.congr
  filter_upwards [he] with s hs
  exact (hmatch _ hs).2

theorem frequently_hillRealGapHalfLength_ne_zero_at
    (p : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ᶠ v : RealPeriodOneHillPotential in 𝓝 p,
      hillRealGapHalfLength v.val v.property.1 v.property.2 (n : ℕ) ≠ 0 := by
  intro hc
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by rw [map_zero]; exact Submodule.zero_mem _
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff
      (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    intro k
    simp only [map_zero,lp.coeFn_zero,Pi.zero_apply]
  obtain ⟨v,hv⟩ := (frequently_hillRealGapHalfLength_ne_zero h0q h0r n).exists
  let f : ℝ → ℂ := fun s => (2*(hillRealGapHalfLength (hillPhysicalRealLine p v s).val
    (hillPhysicalRealLine p v s).property.1 (hillPhysicalRealLine p v s).property.2
    (n : ℕ) : ℂ))^2
  have hf : AnalyticOnNhd ℝ f univ := fun t _ => analyticAt_hillRealGapSquare_realLine p v n t
  have hline0 : hillPhysicalRealLine p v 0 = p := by
    apply Subtype.ext
    simp only [hillPhysicalRealLine,ofReal_zero,zero_smul,add_zero]
  have hline1 : hillPhysicalRealLine p v 1 = v := by
    apply Subtype.ext
    simp only [hillPhysicalRealLine,ofReal_one,one_smul,add_sub_cancel]
  have ht := (continuous_hillPhysicalRealLine p v).tendsto 0
  rw [hline0] at ht
  have hz : f =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [ht.eventually hc] with s hs
    simp only [f,not_ne_iff.mp hs,ofReal_zero,mul_zero,zero_pow (by norm_num : 2 ≠ 0)]
  have he := hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ
    (mem_univ (0 : ℝ)) hz (mem_univ (1 : ℝ))
  change (2*(_ : ℂ))^2 = 0 at he
  simp only [hline1] at he
  have hgap : (hillRealGapHalfLength v.val v.property.1 v.property.2 (n : ℕ) : ℂ) = 0 :=
    (mul_eq_zero.mp (sq_eq_zero_iff.mp he)).resolve_left (by norm_num)
  exact hv (ofReal_injective hgap)

end NLS.KdV
