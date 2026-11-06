import NLS.Articles.KdVKdV2Frequencies.GlobalRoughRealInverse

/-! # Full source convergence from the SAME global real weak inverse

The literal normalized source/target charts and the one global weak
homeomorphism turn convergence of full signed outputs into strong
H-minus-one convergence of actual real mean-zero sources.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Convergence of full signed targets implies actual strong rough source
convergence, without any initial source compactness or regularity premise. -/
theorem tendsto_real_meanZero_source_of_signed_tendsto
    (D : GlobalRoughAbelianForwardData) {ι : Type*} {l : Filter ι}
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (r : ι → PeriodOneHminusOne) (hr : ∀ i, IsRealPeriodOneHminusOne (r i))
    (hrm : ∀ i, (r i).val 0=0)
    (h : Tendsto (fun i => D.signed (r i)) l (𝓝 (D.signed q))) :
    Tendsto r l (𝓝 q) := by
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  let T := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let a : physicalRealDeletedSubmodule :=
    ⟨P q,meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1)) q hq⟩
  let b : ι → physicalRealDeletedSubmodule := fun i =>
    ⟨P (r i),meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1)) (r i) (hr i)⟩
  have hLa : L a.val=q := WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have hLb (i : ι) : L (b i).val=r i := WeightedCoeff.meanZeroWeightedLift_projection _ (r i) (hrm i)
  have hFa : (D.realWeakHomeomorph a).val=T (D.signed q) := by
    change T (D.signed (L a.val))=_
    rw [hLa]
  have hFb (i : ι) : (D.realWeakHomeomorph (b i)).val=T (D.signed (r i)) := by
    change T (D.signed (L (b i).val))=_
    rw [hLb]
  have ht : Tendsto (fun i => D.realWeakHomeomorph (b i)) l (𝓝 (D.realWeakHomeomorph a)) := by
    apply tendsto_subtype_rng.mpr
    have hh := T.continuous.continuousAt.tendsto.comp h
    simpa only [←hFa,←hFb,Function.comp_def] using hh
  have hb : Tendsto b l (𝓝 a) := by
    have hh := D.realWeakHomeomorph.symm.continuous.continuousAt.tendsto.comp ht
    simpa only [Homeomorph.symm_apply_apply,Function.comp_def] using hh
  have hc : Continuous (fun u : physicalRealDeletedSubmodule => L u.val) :=
    L.continuous.comp continuous_subtype_val
  have hh := hc.continuousAt.tendsto.comp hb
  simpa only [hLa,hLb,Function.comp_def] using hh

/-- The SAME global signed coordinates have exactly the ORIGINAL action
product at EVERY physical mean-zero L2 source, with no factor of two. -/
theorem signed_product_eq_original_action (D : GlobalRoughAbelianForwardData)
    (p : hillRealMeanZeroSourceSubmodule) (n : ℕ+) :
    (D.signed (hillOriginalHminusSource p.val.val)).val (n : ℤ)*
      (D.signed (hillOriginalHminusSource p.val.val)).val (-(n : ℤ))=
      (hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0 : ℂ) := by
  rw [D.signed_real _ (hillOriginalHminusSource_real _ p.val.property.2),
    D.original_global_birkhoff_agreement,hillOriginalBirkhoffAbelianCoordinate_eq_original]
  rw [mul_comm,←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (norm_sq_hillDirichletAbelianCoordinate p.val.val p.val.property.1 p.val.property.2
      (by simp) (by intro j; simp) n n.pos)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
