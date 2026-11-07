import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralEndpointHitting

/-! Finite actual endpoint moves with the intrinsic complete angle-pair
value retained. Continuity on the full compact original isospectral set
will then permit simultaneous placement of all countably many terminals. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem continuous_originalPeriodOneCoefficients : Continuous originalPeriodOneCoefficients :=
  periodOneOriginalExtract.continuous.comp continuous_subtype_val

theorem originalHillGapSquare_eq_of_isospectral (q p : OriginalHminusOnePotential)
    (hp : p ∈ originalIsospectralSet q) (n : ℕ+) :
    hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients p)=
      hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) := by
  rw [originalCanonicalGapSquare_eq,originalCanonicalGapSquare_eq,originalCanonicalGapValues_isospectral q p hp]

theorem continuous_originalHillDirichletSheet (k : ℕ+) :
    Continuous (fun p : OriginalHminusOnePotential => hillHminusDirichletSheet k (originalPeriodOneCoefficients p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (analyticOnNhd_hillHminusDirichletSheet k _ (real_mem_hillHminusCanonicalDirichletDomain _
    (originalPeriodOneCoefficients_real p))).continuousAt.comp continuous_originalPeriodOneCoefficients.continuousAt

theorem continuousOn_originalHillCompletePhasePair (n m : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    ContinuousOn (fun p : OriginalHminusOnePotential => hillHminusCompletePhasePairBracket n m
      (originalPeriodOneCoefficients p)) (originalIsospectralSet q) := by
  intro p hp
  have hpn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients p) ≠ 0 := by
    rwa [originalHillGapSquare_eq_of_isospectral q p hp n]
  have hpm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients p) ≠ 0 := by
    rwa [originalHillGapSquare_eq_of_isospectral q p hp m]
  have hdom := real_mem_hillHminusOffIndexAnalyticDomain _ (originalPeriodOneCoefficients_real p)
  exact ((analyticOnNhd_hillHminusCompletePhasePairBracket n m _ ⟨⟨hdom,hpn⟩,⟨hdom,hpm⟩⟩).continuousAt.comp
    continuous_originalPeriodOneCoefficients.continuousAt).continuousWithinAt

theorem exists_originalHill_finite_endpoints_same_pair (n m : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) (A : Finset ℕ+) :
    ∃ p ∈ originalIsospectralSet q,
      hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients p)=
        hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients q) ∧
      ∀ j ∈ A, hillHminusDirichletSheet j (originalPeriodOneCoefficients p)=0 := by
  classical
  induction A using Finset.induction with
  | empty => exact ⟨q,mem_originalIsospectralSet_self q,rfl,by simp⟩
  | @insert k A _ ih =>
    obtain ⟨p,hp,hpair,hplaced⟩ := ih
    obtain ⟨t,ht,_⟩ := exists_originalHillSpectralFlow_endpoint k p
    let r := originalHillSpectralFlow k p t
    have hr : r ∈ originalIsospectralSet q := by
      apply (mem_originalIsospectralSet_iff_discriminant_eq q r).mpr
      exact ((mem_originalIsospectralSet_iff_discriminant_eq p r).mp
        (originalHillSpectralFlow_mem_isospectral k p t)).trans
          ((mem_originalIsospectralSet_iff_discriminant_eq q p).mp hp)
    have hpn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients p) ≠ 0 := by
      rwa [originalHillGapSquare_eq_of_isospectral q p hp n]
    have hpm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients p) ≠ 0 := by
      rwa [originalHillGapSquare_eq_of_isospectral q p hp m]
    refine ⟨r,hr,(originalHillSpectralFlow_completePhasePair n m k p hpn hpm t).trans hpair,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ht
    · by_cases hjk : j=k
      · subst j
        exact ht
      · have he := congrArg (fun z : ℂ × ℂ × ℂ => z.2.2)
          (originalHillSpectralFlow_other_terminal j k hjk p t)
        exact he.trans (hplaced j hj)

end NLS.Articles.KdVPseudomeasures
