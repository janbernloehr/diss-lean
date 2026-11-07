import NLS.Articles.KdVPseudomeasures.OriginalEndpointMembership
import NLS.Articles.KdVPseudomeasures.OriginalFinitePCompactCover

/-!
# Uniform original endpoint bounds from actual spectral gaps

A compact finite-p Miura image supplies one base norm bound for the ENTIRE
original isospectral family. The verified uniform endpoint bootstrap then
uses the common original gap sequence to obtain Lemma 2.21 without assuming
endpoint regularity or a stronger norm bound on the original family.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original endpoint gap hypothesis gives one common admissible lower
finite-p space and one uniform norm bound for the ENTIRE original isospectral
set. Every representative is the identical entire physical distribution. -/
theorem exists_uniform_originalIsospectral_lower_finiteP_bound_of_endpoint_gaps
    (q : OriginalHminusOnePotential) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n:ℂ)*originalCanonicalGapValues q n) ⊤) :
    ∃ b : ℝ, AdmissiblePredualOrder b ∧ r < b ∧
      ∃ (p : ℝ≥0∞) (hp2 : 2 ≤ p), p ≠ ⊤ ∧ 1 < b*p.toReal ∧
        ∃ R : ℝ, 0 ≤ R ∧
          letI : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
          ∀ v ∈ originalIsospectralSet q,
            ∃ Q : FourierLebesgueSpace (2:ℝ) (-b) p, Q.val = v.val.val ∧ ‖Q‖ ≤ R := by
  obtain ⟨a,ha,hra,p,hp2,hp,hΔ,hap,_⟩ :=
    exists_original_isospectral_finiteP_membership_of_endpoint_gaps q r hr hgap
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
  let b := (a+1/2)/2
  have hab : a < b := by dsimp [b]; linarith only [ha.2]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith only [ha.1]
  have hbhalf : b < 1/2 := by dsimp [b]; linarith only [ha.2]
  have hpR : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hbp : 1 < b*p.toReal := hap.trans (mul_lt_mul_of_pos_right hab hpR)
  let g : WeightedCoeff (Weight.sobolev (-r)) ⊤ := ⟨originalCanonicalGapValues q,hgap⟩
  have hth : 1 < (-r-(-a))*p.toReal := by nlinarith only [hΔ]
  let g' := WeightedCoeff.endpointLowerInclusion (-r) (-a) hp hth g
  have hga : Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*originalCanonicalGapValues q n) p := by
    have h := g'.property
    change Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*g'.val n) p at h
    have he (n : ℤ) : g'.val n = originalCanonicalGapValues q n :=
      WeightedCoeff.endpointLowerInclusion_apply (-r) (-a) hp hth g n
    simpa only [he] using h
  obtain ⟨R,hR,hbound⟩ := exists_uniform_originalIsospectral_finiteP_bound q hp hp2 a b hab
    (by linarith only [hbhalf]) hbp hga
  exact ⟨b,⟨hb0,hbhalf⟩,hra.trans hab,p,hp2,hp,hbp,R,hR,hbound⟩

/-- Source Lemma 2.21 on the full original H-minus-one domain: one target
endpoint norm bound precedes EVERY member of the original isospectral set.
No endpoint membership or uniform-bound premise is imposed on that set. -/
theorem sourceLemma2_21 (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n:ℂ)*originalCanonicalGapValues q n) ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ originalIsospectralSet q,
      ∃ a : Potential r, a.val.val = v.val.val ∧ ‖a.val‖ ≤ C := by
  obtain ⟨b,hb,hrb,p,hp2,_,_,R,hR,hbound⟩ :=
    exists_uniform_originalIsospectral_lower_finiteP_bound_of_endpoint_gaps q r hr hgap
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
  obtain ⟨G,hG,hgapBound⟩ := NLS.exists_norm_bound_of_memlp hgap
  obtain ⟨C,hC,hbootstrap⟩ := source_uniform_endpoint_bootstrap b hb r hr.1 hrb.le R G hR hG
  refine ⟨C,hC,fun v hv => ?_⟩
  obtain ⟨Q,hQ,hQn⟩ := hbound v hv
  obtain ⟨B,hB,hBn⟩ := exists_of_endpoint_bound (Weight.sobolev (-b)) v.val.val R hR (fun k => by
    have h := weight_mul_norm_coefficient_le (Weight.sobolev (-b)) p Q k
    rw [hQ] at h
    exact h.trans hQn)
  have hBphys : B.val.IsRealMeanZeroPeriodOne := by rw [hB]; exact v.property
  let z : Potential b := ⟨B,hBphys⟩
  have hzOriginal : sourceOriginalPotential b hb z = v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (sourceOriginalPotential_val b hb z).trans hB
  have hzGap : sourceCanonicalGapValues b hb z = originalCanonicalGapValues q :=
    (originalCanonicalGapValues_sourceOriginalPotential b hb z).symm.trans
      ((congrArg originalCanonicalGapValues hzOriginal).trans
        (originalCanonicalGapValues_isospectral q v hv))
  have hzGapBound : ∀ n : ℕ, 1 ≤ n →
      Weight.sobolev (-r) (n:ℤ)*‖sourceCanonicalGapValues b hb z (n:ℤ)‖ ≤ G := by
    intro n _
    rw [hzGap]
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-r)).positive (n:ℤ))] using hgapBound (n:ℤ)
  obtain ⟨a,ha,han⟩ := hbootstrap z hBn hzGapBound
  exact ⟨a,ha.trans hB,han⟩

end NLS.Articles.KdVPseudomeasures
