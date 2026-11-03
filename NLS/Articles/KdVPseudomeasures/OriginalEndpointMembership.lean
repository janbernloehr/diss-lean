import NLS.Articles.KdVPseudomeasures.OriginalFinitePInverse
import NLS.Articles.KdVPseudomeasures.SpectralEndpointBootstrap

/-!
# Theorem 2.2(i)-(ii) on the entire original domain

Actual endpoint gap regularity gives finite-p membership of every original
isospectral potential. The verified endpoint bootstrap is then applied to
each such potential. A uniform isospectral norm bound, and hence part(iii),
are separate obligations and are not inferred from individual membership.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Source Theorem2.2(ii): the ENTIRE original H-minus-one isospectral set
belongs to the target endpoint space, retaining all original distributions
and physical constraints. No base endpoint or uniform-bound premise occurs. -/
theorem sourceTheorem2_2_ii (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev (-r) k:ℂ)*originalCanonicalGapValues q k) ⊤) :
    ∀ v : OriginalHminusOnePotential, v ∈ originalIsospectralSet q →
      ∃ a : Potential r, a.val.val = v.val.val := by
  obtain ⟨t,ht,htr,p,hp2,hp,_,_,hfinite⟩ :=
    exists_original_isospectral_finiteP_membership_of_endpoint_gaps q r hr hgap
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
  obtain ⟨G,hG,hgapBound⟩ := NLS.exists_norm_bound_of_memlp hgap
  intro v hv
  obtain ⟨Q,hQ⟩ := hfinite v hv
  obtain ⟨B,hB,_⟩ := exists_of_endpoint_bound (Weight.sobolev (-t)) v.val.val ‖Q‖
    (norm_nonneg Q) (fun k => by
      have hh := weight_mul_norm_coefficient_le (Weight.sobolev (-t)) p Q k
      simpa only [hQ] using hh)
  have hBphys : B.val.IsRealMeanZeroPeriodOne := by rw [hB]; exact v.property
  let b : Potential t := ⟨B,hBphys⟩
  have hbOriginal : sourceOriginalPotential t ht b = v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (sourceOriginalPotential_val t ht b).trans hB
  have hbGap : sourceCanonicalGapValues t ht b = originalCanonicalGapValues q :=
    (originalCanonicalGapValues_sourceOriginalPotential t ht b).symm.trans
      ((congrArg originalCanonicalGapValues hbOriginal).trans
        (originalCanonicalGapValues_isospectral q v hv))
  have hbGapBound : ∀ n : ℕ, 1 ≤ n →
      Weight.sobolev (-r) (n:ℤ)*‖sourceCanonicalGapValues t ht b (n:ℤ)‖ ≤ G := by
    intro n _
    rw [hbGap]
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-r)).positive (n:ℤ))] using hgapBound (n:ℤ)
  obtain ⟨_,_,hbootstrap⟩ := source_uniform_endpoint_bootstrap t ht r hr.1 htr.le
    ‖b.val‖ G (norm_nonneg b.val) hG
  obtain ⟨a,ha,_⟩ := hbootstrap b le_rfl hbGapBound
  exact ⟨a,ha.trans hB⟩

/-- Source Theorem2.2(i): actual endpoint gap regularity implies endpoint
regularity of the identical original H-minus-one potential. -/
theorem sourceTheorem2_2_i (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev (-r) k:ℂ)*originalCanonicalGapValues q k) ⊤) :
    ∃ a : Potential r, a.val.val = q.val.val :=
  sourceTheorem2_2_ii q r hr hgap q (mem_originalIsospectralSet_self q)

end NLS.Articles.KdVPseudomeasures
