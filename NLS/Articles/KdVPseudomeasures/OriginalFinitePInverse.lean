import NLS.Articles.KdVPseudomeasures.OriginalMiuraGapComparison
import NLS.KdV.PeriodOneOriginalRegularity
import NLS.SequenceSpaces.PeriodOneMiuraFiniteRegularity
import NLS.ZakharovShabat.SourceSobolevGapRegularity
import NLS.ZakharovShabat.ExponentSourcePotentials

/-!
# Original finite-p inverse spectral regularity

Weighted gaps of the actual full original Hill operator yield regularity
of the identical original smooth-test distribution. The proof transfers
the actual signed Dirac gaps, applies the verified source inverse theorem,
and uses the exact rough Miura regularity equivalence.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ZakharovShabat NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Actual original gap regularity implies original finite-p potential
regularity. No endpoint membership or isospectral bound is assumed.
The strict negative-weight threshold controls the rough quadratic term. -/
theorem exists_original_finiteP_realization_of_gap
    (q : OriginalHminusOnePotential) (s : ℝ) (hs : -1 ≤ s) (hs0 : s ≤ 0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hsp : 1 < (-s)*p.toReal)
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k) p) :
    ∃ Q : FourierLebesgueSpace (2:ℝ) s p, Q.val = q.val.val := by
  obtain ⟨c,_,_,u,himage⟩ := exists_real_periodOneMiura_shift
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) 0
  have himage' : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [ofReal_pow] using himage
  have hD := memlp_miuraDiracGap_of_original_gap q u (c^2) s himage' hgap
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : (1:ℝ≥0∞) < 2) hp2
  let φ := CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal u.val)
  have hφ : IsRealType (CoeffPair.toMax p φ) := by
    intro n
    change φ.snd n = conj (φ.fst (-n))
    simp only [φ,CoeffPair.exponentInclusion_snd,CoeffPair.exponentInclusion_fst,
      hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,Coeff.exponentInclusion_apply]
    simpa only [neg_neg] using u.property (-n)
  let ψ : realTypeSourceSubmodule p := ⟨φ,hφ⟩
  have hends := canonicalPeriodicEndpoints_periodOne_exponent
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hp (by norm_num) hp1 hp2 (hillMiuraDiagonal u.val)
  have hgp : Memℓp (fun k : ℤ => (Weight.sobolev (s+1) k:ℂ)*
      sourcePeriodicGapDisplacement hp hp1 φ k) p := by
    have he : (fun k : ℤ => (Weight.sobolev (s+1) k:ℂ)*sourcePeriodicGapDisplacement hp hp1 φ k) =
        fun k => (Weight.sobolev (s+1) k:ℂ)*
          (hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k) := by
      funext k
      rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
      have hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) k =
          hillMiuraDiracLeft u.val k := (congrFun hends.1 k).symm
      have hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) k =
          hillMiuraDiracRight u.val k := (congrFun hends.2 k).symm
      rw [hl,hr]
    rw [he]
    exact hD
  have hreg := source_mem_sobolev_of_gap hp hp1 ψ (s+1) (by linarith) hgp
  have hu : Memℓp (fun k : ℤ => (Weight.sobolev (s+1) k:ℂ)*u.val k) p := by
    simpa only [ψ,φ,CoeffPair.exponentInclusion_fst,hillMiuraDiagonal_fst,
      Coeff.exponentInclusion_apply] using hreg.1
  have hqreg := (periodOneMiura_shift_memlp_iff (-s) hp hp2 hsp u.val
    (originalPeriodOneCoefficients q) ((c:ℂ)^2) himage).mpr
      (by simpa only [neg_neg,sub_neg_eq_add,add_comm] using hu)
  have hqreg' : Memℓp (fun k : ℤ => (Weight.sobolev s k:ℂ)*
      (originalPeriodOneCoefficients q).val k) p := by simpa only [neg_neg] using hqreg
  obtain ⟨Q,hQ⟩ := exists_periodOneOriginal_regular_realization (originalPeriodOneCoefficients q) s hs0 hqreg'
  refine ⟨Q,?_⟩
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hQ

/-- The same original finite-p regularity holds for every member of the
ENTIRE original isospectral set. This is membership, not a uniform bound. -/
theorem originalIsospectralSet_finiteP_realization_of_gap
    (q : OriginalHminusOnePotential) (s : ℝ) (hs : -1 ≤ s) (hs0 : s ≤ 0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hsp : 1 < (-s)*p.toReal)
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k) p)
    (v : OriginalHminusOnePotential) (hv : v ∈ originalIsospectralSet q) :
    ∃ Q : FourierLebesgueSpace (2:ℝ) s p, Q.val = v.val.val := by
  apply exists_original_finiteP_realization_of_gap v s hs hs0 hp hp2 hsp
  rw [originalCanonicalGapValues_isospectral q v hv]
  exact hgap

/-- The article's endpoint gap hypothesis supplies a single admissible lower
order and finite exponent for the ENTIRE original isospectral set. The chosen
exponent also satisfies the strict quadratic-term summability threshold.
This asserts common-space membership, not a common norm bound or compactness. -/
theorem exists_original_isospectral_finiteP_membership_of_endpoint_gaps
    (q : OriginalHminusOnePotential) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun k : ℤ => (Weight.sobolev (-r) k:ℂ)*originalCanonicalGapValues q k) ⊤) :
    ∃ t : ℝ, AdmissiblePredualOrder t ∧ r < t ∧
      ∃ (p : ℝ≥0∞) (hp2 : 2 ≤ p), p ≠ ⊤ ∧ 1 < (t-r)*p.toReal ∧ 1 < t*p.toReal ∧
        letI : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
        ∀ v : OriginalHminusOnePotential, v ∈ originalIsospectralSet q →
          ∃ Q : FourierLebesgueSpace (2:ℝ) (-t) p, Q.val = v.val.val := by
  let t : ℝ := (r+1/2)/2
  have ht0 : 0 < t := by dsimp [t]; linarith [hr.1]
  have htr : r < t := by dsimp [t]; linarith [hr.2]
  have ht1 : t < 1/2 := by dsimp [t]; linarith [hr.2]
  have hd : 0 < t-r := sub_pos.mpr htr
  obtain ⟨M,hM⟩ := exists_nat_gt (max 2 (max (1/(t-r)) (1/t)))
  have hM2 : 2 ≤ M := by
    have hh : (2:ℝ) ≤ M := (le_max_left _ _).trans hM.le
    exact_mod_cast hh
  let p : ℝ≥0∞ := M
  have hp2 : 2 ≤ p := by
    change (2:ℝ≥0∞) ≤ (M:ℝ≥0∞)
    exact_mod_cast hM2
  have hp : p ≠ ⊤ := by simp [p]
  have hpR : p.toReal = (M:ℝ) := by simp [p]
  have hΔ : 1 < (t-r)*p.toReal := by
    have hh : 1/(t-r) < (M:ℝ) :=
      (le_max_of_le_right (le_max_left _ _)).trans_lt hM
    rw [hpR]
    have hb := (div_lt_iff₀ hd).mp hh
    nlinarith
  have hT : 1 < t*p.toReal := by
    have hh : 1/t < (M:ℝ) :=
      (le_max_of_le_right (le_max_right _ _)).trans_lt hM
    rw [hpR]
    have hb := (div_lt_iff₀ ht0).mp hh
    nlinarith
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp2⟩
  let a : WeightedCoeff (Weight.sobolev (-r)) ⊤ := ⟨originalCanonicalGapValues q,hgap⟩
  have hthresh : 1 < (-r-(-t))*p.toReal := by nlinarith
  let b := WeightedCoeff.endpointLowerInclusion (-r) (-t) hp hthresh a
  have hb : Memℓp (fun k : ℤ => (Weight.sobolev (-t) k:ℂ)*originalCanonicalGapValues q k) p := by
    have hh := b.property
    change Memℓp (fun k : ℤ => (Weight.sobolev (-t) k:ℂ)*b.val k) p at hh
    have hraw (k : ℤ) : b.val k = originalCanonicalGapValues q k :=
      WeightedCoeff.endpointLowerInclusion_apply (-r) (-t) hp hthresh a k
    simpa only [hraw] using hh
  refine ⟨t,⟨ht0.le,ht1⟩,htr,p,hp2,hp,hΔ,hT,?_⟩
  intro v hv
  exact originalIsospectralSet_finiteP_realization_of_gap q (-t) (by linarith) (by linarith)
    hp hp2 (by simpa only [neg_neg] using hT) hb v hv

end NLS.Articles.KdVPseudomeasures
