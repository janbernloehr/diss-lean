import NLS.ZakharovShabat.RealGapArcoshRadicand
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation

/-!
# Reality of deleted periodic-pair products

Every finite normalized deleted product is real on the real axis when
its endpoint sequences are real. Locally uniform convergence carries
this property to the entire product, including at the deleted pair.
-/

noncomputable section
open Set Filter Topology Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each finite deleted endpoint-pair product is real when all
periodic endpoints are real. -/
theorem deletedSpectralPairPartialProduct_im_eq_zero_of_real_roots
    (ξ η : ℤ → ℂ) (hξ : ∀ k, (ξ k).im = 0)
    (hη : ∀ k, (η k).im = 0) (n : ℤ) (N : ℕ) (x : ℝ) :
    (deletedSpectralPairPartialProduct ξ η n N x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hden (k : ℤ) : conj (spectralPairDenominator k) =
      spectralPairDenominator k := by
    unfold spectralPairDenominator
    split_ifs <;> simp
  have hfactor (k : ℤ) : conj (spectralPairFactor ξ η x k) =
      spectralPairFactor ξ η x k := by
    rw [spectralPairFactor_eq_div]
    simp only [map_div₀, map_mul, map_sub, conj_ofReal,
      (Complex.conj_eq_iff_im.mpr (hξ k)),
      (Complex.conj_eq_iff_im.mpr (hη k)), hden]
  unfold deletedSpectralPairPartialProduct
  rw [map_div₀, map_prod]
  simp only [hfactor,hden]

/-- The entire deleted product is real on the real axis for real
endpoint sequences with the required `ℓp` displacements. -/
theorem deletedSpectralPairProduct_im_eq_zero_of_real_roots
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξlp : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hηlp : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p)
    (hξ : ∀ k, (ξ k).im = 0) (hη : ∀ k, (η k).im = 0)
    (n : ℤ) (x : ℝ) :
    (deletedSpectralPairProduct ξ η n x).im = 0 := by
  have ht := (tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp ξ η
    hξlp hηlp n).tendsto_at (mem_univ (x:ℂ))
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  have heq (N : ℕ) : conj (deletedSpectralPairPartialProduct ξ η n N x) =
      deletedSpectralPairPartialProduct ξ η n N x :=
    Complex.conj_eq_iff_im.mpr
      (deletedSpectralPairPartialProduct_im_eq_zero_of_real_roots ξ η hξ hη n N x)
  simp only [Function.comp_def] at hc
  simp_rw [heq] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

/-- The canonical deleted periodic-pair product of a real-type
potential has real value at every real spectral parameter. -/
theorem canonicalDeletedPeriodicProduct_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) (x : ℝ) :
    (canonicalDeletedPeriodicProduct hp hp1 φ heven n x).im = 0 := by
  let ξ := canonicalPeriodicLeft hp hp1 φ heven
  let η := canonicalPeriodicRight hp hp1 φ heven
  exact deletedSpectralPairProduct_im_eq_zero_of_real_roots hp ξ η
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.left_displacement
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.right_displacement
    (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ heven hreal k).1)
    (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ heven hreal k).2) n x

/-- A real point between the canonical endpoints belongs to the
corresponding complex source gap segment. -/
theorem sourcePeriodicSegment_mem_of_realIcc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (x:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ n := by
  let l := canonicalPeriodicLeft hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hl : ((l.re : ℝ) : ℂ) = l := by
    have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
        (isRealType_periodOnePotential ψ hreal) n).1
    apply Complex.ext
    · simp
    · change 0 = l.im
      exact him.symm
  have hr : ((r.re : ℝ) : ℂ) = r := by
    have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
        (isRealType_periodOnePotential ψ hreal) n).2
    apply Complex.ext
    · simp
    · change 0 = r.im
      exact him.symm
  obtain ⟨a,b,ha,hb,hab,heq⟩ := (Icc_subset_segment hx)
  change (x:ℂ) ∈ segment ℝ l r
  refine ⟨a,b,ha,hb,hab,?_⟩
  rw [← hl,← hr]
  have hc := congrArg (fun y : ℝ => (y:ℂ)) heq
  simpa only [Complex.ofReal_add, Complex.ofReal_mul,
    Complex.real_smul, smul_eq_mul] using hc

/-- At a real-type source, the deleted pair product is strictly
positive on the whole of each open real gap, endpoints included. -/
theorem canonicalDeletedPeriodicProduct_re_pos_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n x).re := by
  let φ := periodOnePotential ψ
  let a := (canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n).re
  let G (y : ℝ) := (canonicalDeletedPeriodicProduct hp hp1 φ
    (periodOnePotential_mem ψ) n y).re
  have hGcont : Continuous G := by
    have h := (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ
      (periodOnePotential_mem ψ) n).continuousOn
    exact continuous_re.comp ((continuousOn_univ.mp h).comp continuous_ofReal)
  have hGnonneg : 0 ≤ G x := by
    have hclosed : IsClosed {y : ℝ | 0 ≤ G y} :=
      isClosed_le continuous_const hGcont
    have hsub : Ioo a b ⊆ {y : ℝ | 0 ≤ G y} := by
      intro y hy
      exact (canonicalDeletedPeriodicProduct_re_pos_on_realGap_interior hp hp1
        φ (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal)
        n y hy).le
    have hcl := closure_minimal hsub hclosed
    rw [closure_Ioo hopen.ne] at hcl
    exact hcl hx
  have hGim : (canonicalDeletedPeriodicProduct hp hp1 φ
      (periodOnePotential_mem ψ) n x).im = 0 :=
    canonicalDeletedPeriodicProduct_im_eq_zero_of_realType hp hp1 φ
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n x
  obtain ⟨W,_,_,hrealW,hdisjoint⟩ :=
    exists_global_source_disjoint_periodicSegments hp hp1
  have hψW : ψ ∈ W := hrealW hreal
  have hseg : (x:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ n :=
    sourcePeriodicSegment_mem_of_realIcc hp hp1 ψ hreal n x hx
  have hdom : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro m hmn hmseg
    exact Set.disjoint_left.mp
      (hdisjoint ψ hψW n m (Ne.symm hmn)) hseg hmseg
  have hGne : canonicalDeletedPeriodicProduct hp hp1 φ
      (periodOnePotential_mem ψ) n x ≠ 0 :=
    canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain
      hp hp1 ψ n x hdom
  have hGre : G x ≠ 0 := by
    intro hzero
    apply hGne
    apply Complex.ext <;> simp [G,hzero,hGim]
  exact lt_of_le_of_ne hGnonneg (Ne.symm hGre)

/-- Compactness upgrades closed-gap positivity to one positive lower
bound for the deleted factor. -/
theorem exists_pos_lower_bound_deletedPeriodicProduct_re_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Icc
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re,
        m ≤ (canonicalDeletedPeriodicProduct hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n x).re := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let G (x : ℝ) := (canonicalDeletedPeriodicProduct hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n x).re
  have hGcont : ContinuousOn G (Icc a b) := by
    have h := (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n).continuousOn
    exact (continuous_re.comp ((continuousOn_univ.mp h).comp
      continuous_ofReal)).continuousOn
  have hne : (Icc a b).Nonempty := ⟨a,⟨le_rfl,hopen.le⟩⟩
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn hne hGcont
  refine ⟨G x,canonicalDeletedPeriodicProduct_re_pos_on_realGap
    hp hp1 ψ hreal n hopen x hx,?_⟩
  intro y hy
  exact hmin hy

end NLS.ZakharovShabat
