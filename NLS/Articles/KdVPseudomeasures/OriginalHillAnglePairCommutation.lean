import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralCompactTransport
import NLS.Articles.KdVPseudomeasures.OriginalHillIntrinsicAngleEndpoint

/-! Full actual angle-pair commutation on the original physical source.
Every finite set of terminals can be placed at endpoints by actual flows.
Compactness and the finite intersection property place all terminals at
endpoints while retaining the complete intrinsic pair value. No density
of finite-gap potentials or convergence premise is assumed. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem original_Hill_complete_angle_pair_Gardner_commute (n m : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients q)=0 := by
  let K := originalIsospectralSet q
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_originalIsospectralSet q)
  let H (p : OriginalHminusOnePotential) := hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients p)
  have hH : Continuous (fun p : K => H p.val) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_originalHillCompletePhasePair n m q hn hm)
  let C (j : ℕ+) : Set K :=
    {p | hillHminusDirichletSheet j (originalPeriodOneCoefficients p.val)=0} ∩ {p | H p.val=H q}
  have hC (j : ℕ+) : IsClosed (C j) :=
    (isClosed_eq ((continuous_originalHillDirichletSheet j).comp continuous_subtype_val) continuous_const).inter
      (isClosed_eq hH continuous_const)
  have hfinite (A : Finset ℕ+) : (⋂ j ∈ A, C j).Nonempty := by
    obtain ⟨p,hp,hpair,hzero⟩ := exists_originalHill_finite_endpoints_same_pair n m q hn hm A
    refine ⟨⟨p,hp⟩,?_⟩
    simp only [mem_iInter]
    intro j hj
    exact ⟨hzero j hj,hpair⟩
  obtain ⟨p,hp⟩ := CompactSpace.iInter_nonempty hC hfinite
  have hterminal (j : ℕ+) : hillHminusDirichletSheet j (originalPeriodOneCoefficients p.val)=0 :=
    (mem_iInter.mp hp j).1
  have hpair : H p.val=H q := (mem_iInter.mp hp (1:ℕ+)).2
  have hpn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients p.val) ≠ 0 := by
    rwa [originalHillGapSquare_eq_of_isospectral q p.val p.property n]
  have hpm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients p.val) ≠ 0 := by
    rwa [originalHillGapSquare_eq_of_isospectral q p.val p.property m]
  exact hpair.symm.trans (original_Hill_complete_angle_pair_zero_at_all_endpoints p.val n m hpn hpm hterminal)

end NLS.Articles.KdVPseudomeasures
