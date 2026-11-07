import NLS.Articles.KdVPseudomeasures.SourceComplexCouplingComparison
import NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps
import NLS.Articles.KdVPseudomeasures.SpectralInverseRestriction

/-! Full complex Lemma 2.20 for the actual adapted Fourier map and the
actual original lexicographic gaps. The uniform cutoff satisfies (36). -/
noncomputable section
open Set Filter Topology NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_exists_threshold36 (r C m : ℝ) (hr1 : r<1/2) (hm : 1≤m) :
    ∃ M : ℕ, 2≤M ∧ ∀ n : ℕ, M≤n → 8*C/(n:ℝ)^(1/2-r)≤1/(16*m) := by
  have hp : 0<1/2-r := by linarith
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(1/2-r)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (128*C*m)))
  refine ⟨max M 2,le_max_right _ _,?_⟩
  intro n hn
  have hn2 : 2≤n := (le_max_right M 2).trans hn
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hnp (1/2-r)) (by linarith : (0:ℝ)<16*m)).mpr
  have hh := hM n ((le_max_left M 2).trans hn)
  nlinarith

def SourceLemma220OmegaComparison (r : ℝ) (hr : AdmissiblePredualOrder r) (m : ℝ) (M : ℕ) : Prop :=
  ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖≤m → q.val (mode 0)=0 →
    ∀ n : ℕ, M≤n →
      let R := sourceAdaptedFourier r hr M q
      let b := R.val (mode (-(2*(n:ℤ))))
      let c := R.val (mode (2*(n:ℤ)))
      c≠0 → (1:ℝ)/9≤‖b/c‖ → ‖b/c‖≤9 →
        ‖b*c‖≤‖sourceComplexCanonicalGapValues r hr q (n:ℤ)‖^2 ∧
        ‖sourceComplexCanonicalGapValues r hr q (n:ℤ)‖^2≤9*‖b*c‖

/-- The printed c'_s and one cutoff M_(m,s) are chosen before every
complex source potential in B_m and all high canonical spectral slots. -/
theorem sourceLemma2_20 (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ C : ℝ, 1≤C ∧ sourceCoefficientConstant r≤C ∧ ∀ m : ℝ, 1≤m →
      ∃ M : ℕ, 2≤M ∧ (∀ n : ℕ, M≤n → 8*C/(n:ℝ)^(1/2-r)≤1/(16*m)) ∧
        SourceLemma220OmegaComparison r hr m M := by
  obtain ⟨C,hC,hcs,_⟩ := sourceLemma2_10 r hr.1 hr.2
  refine ⟨C,hC,hcs,?_⟩
  intro m hm
  obtain ⟨M₀,hM₀,hthreshold⟩ := source_exists_threshold36 r C m hr.2 hm
  obtain ⟨N,hN,_,hlabel⟩ := source_uniform_canonical_complex_labels_with_contraction r hr m
  let M := max M₀ N
  have hM2 : 2≤M := hM₀.trans (le_max_left _ _)
  have hMthreshold (n : ℕ) (hn : M≤n) : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m) :=
    hthreshold n ((le_max_left _ _).trans hn)
  have hcut (n : ℕ) (hn : 1≤n) (hMn : M≤n) :
      endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*m)≤1/2 := by
    have hh := source_threshold36_small r C m hr.2 hcs hm n hn (hMthreshold n hMn) m (by linarith) le_rfl
    unfold sourceCoefficientConstant at hh
    nlinarith
  refine ⟨M,hM2,hMthreshold,?_⟩
  intro q hq hq0 n hMn
  dsimp only
  intro hcne hratioLow hratioHigh
  have hn2 : 2≤n := hM2.trans hMn
  have hn1 : 1≤n := by omega
  have hqUnit : ‖sourceUnitWeightEquiv r q‖≤m := by simpa only [LinearIsometryEquiv.norm_map] using hq
  have hpair := sourceWeightedAdaptedFourier_high_pair SpectralWeight.one r hr M m (by linarith) hcut
    (sourceUnitWeightEquiv r q) hqUnit n hn1 hMn
  have hp :
      (sourceAdaptedFourier r hr M q).val (mode (-(2*(n:ℤ))))=
        (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn1 q)).2.1 ∧
      (sourceAdaptedFourier r hr M q).val (mode (2*(n:ℤ)))=
        (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn1 q)).2.2 := by
    simpa only [sourceAdaptedFourier_val,sourceAdaptedCouplings,sourceWeightedDiagonalRoot,
      sourceForgetUnitWeight_eq,LinearIsometryEquiv.symm_apply_apply] using hpair
  rw [hp.2] at hcne
  rw [hp.1,hp.2] at hratioLow hratioHigh ⊢
  obtain ⟨p,hl,hrr⟩ := (hlabel q hq).high_pair n ((le_max_right M₀ N).trans hMn)
  have hcore := source_complex_coupling_gap_comparison r hr.1 hr.2 C m hcs hm n hn2 (hMthreshold n hMn)
    (sourceEndpointCoefficients r q) (by simpa only [norm_sourceEndpointCoefficients] using hq)
    (by simpa only [sourceEndpointCoefficients_apply,neg_zero] using hq0) p
  have hh := hcore hcne hratioLow hratioHigh
  have hn0 : (n:ℤ)≠0 := by exact_mod_cast (show n≠0 by omega)
  rw [sourceComplexCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,hl,hrr]
  simpa only [sourceEndpointEntries,sourceDiagonalRoot] using hh

end NLS.Articles.KdVPseudomeasures
