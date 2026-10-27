import NLS.ZakharovShabat.SourceDoubleResolvent
import NLS.ZakharovShabat.SourceUnboundedOperator
import NLS.ZakharovShabat.SourceCorollary3_3
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Section 3 operator setup in the original finite-exponent norms

The full unbounded operator is closed on its actual one-derivative domain.
Young's estimate (1.3) has constant one in the original pair norms, and
both the first resolvent identity and the squared-potential estimate use
the actual source operators. Uniform height decay is an operator-norm
statement; the corresponding vector estimate requires an input norm bound.
The signed second coefficient formula retains integer reflection.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Young's inequality with constant one. For finite p these are the exact source pair norms;
the additional p=infinity instance here uses the legacy maximum pair norm. -/
theorem norm_sourcePotentialFromL1_apply_le (φ : CoeffPair p) (a : CoeffPair 1) :
    ‖sourcePotentialFromL1 φ a‖ ≤ ‖φ‖ * ‖a‖ := by
  have hsplit : sourcePotentialFromL1 φ a =
      WithLp.toLp p (Coeff.convolution φ.fst a.snd, (0 : Coeff p)) +
        WithLp.toLp p ((0 : Coeff p), Coeff.convolution φ.snd a.fst) := by
    apply WithLp.ofLp_injective
    ext j <;> simp
  rw [hsplit]
  calc
    _ ≤ ‖Coeff.convolution φ.fst a.snd‖ + ‖Coeff.convolution φ.snd a.fst‖ := by
      simpa using norm_add_le
        (WithLp.toLp p (Coeff.convolution φ.fst a.snd, (0 : Coeff p)))
        (WithLp.toLp p ((0 : Coeff p), Coeff.convolution φ.snd a.fst))
    _ ≤ ‖φ.fst‖ * ‖a.snd‖ + ‖φ.snd‖ * ‖a.fst‖ :=
      add_le_add (Coeff.norm_convolution_le _ _) (Coeff.norm_convolution_le _ _)
    _ ≤ ‖φ‖ * ‖a.snd‖ + ‖φ‖ * ‖a.fst‖ := by
      gcongr
      · exact WithLp.norm_fst_le _ _
      · exact WithLp.norm_snd_le _ _
    _ = ‖φ‖ * ‖a‖ := by
      have ha : ‖a‖ = ‖a.fst‖ + ‖a.snd‖ := by
        simpa using WithLp.prod_norm_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
      rw [ha]
      ring

/-- Equation (1.3), with the original source input and output norms. -/
theorem sourceEquation1_3 (hp : p ≠ ⊤) (φ f : CoeffPair p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    ‖sourcePotentialFromL1 φ (sourceFreeResolventToL1 hp z hz f)‖ ≤
      ‖φ‖ * ‖sourceFreeResolventToL1 hp z hz f‖ :=
  norm_sourcePotentialFromL1_apply_le φ _

/-- Coefficient-preserving identification of the actual potential/free-resolvent composition. -/
theorem toMax_sourcePotentialFreeResolvent_apply (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    CoeffPair.toMax p (sourcePotentialFromL1 φ (sourceFreeResolventToL1 hp z hz a)) =
      potentialFreeResolvent hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a) := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm
    (potentialFromL1 (CoeffPair.toMax p φ) ((CoeffPair.toMax 1)
      ((CoeffPair.toMax 1).symm (freeResolventToL1 hp z hz (CoeffPair.toMax p a)))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    potentialFreeResolvent_eq_comp_L1]
  rfl

/-- The identity on printed p.23, assuming both inverses exist; no smallness is needed. -/
theorem sourceResolvent_comp_one_sub_potentialFreeResolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : z ∈ sourceResolventSet hp φ) :
    (sourceResolvent hp φ z).comp
      (1 - (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)) =
        sourceFreeResolvent hp z hz := by
  ext a : 1
  change (CoeffPair.toMax p).symm (resolvent hp (CoeffPair.toMax p φ) z
    (CoeffPair.toMax p (a-sourcePotentialFromL1 φ (sourceFreeResolventToL1 hp z hz a)))) =
      (CoeffPair.toMax p).symm (freeResolvent z hz (CoeffPair.toMax p a))
  congr 1
  rw [map_sub, toMax_sourcePotentialFreeResolvent_apply]
  exact congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T (CoeffPair.toMax p a))
    (resolvent_comp_one_sub_potentialFreeResolvent hp (CoeffPair.toMax p φ) z hz
      (by rwa [sourceResolventSet_eq] at hφ))

/-- The actual graph consists precisely of included one-derivative vectors and their images. -/
theorem mem_sourceUnboundedOperator_graph (hp : p ≠ ⊤) (φ : CoeffPair p)
    (x y : CoeffPair p) :
    (x,y) ∈ (sourceUnboundedOperator hp φ).graph ↔
      ∃ f : WeightedCoeffPair (Weight.sobolev 1) p,
        sourceDomainInclusion f = x ∧ sourceOperator hp φ f = y := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u,hx,hy⟩
    obtain ⟨f,rfl⟩ := sourceUnboundedDomainEquiv.surjective u
    exact ⟨f,hx,by simpa using hy⟩
  · rintro ⟨f,hx,hy⟩
    exact ⟨sourceUnboundedDomainEquiv f,hx,by simpa using hy⟩

/-- A bounded spectral inverse characterizes the original operator graph in the base space. -/
theorem mem_sourceUnboundedOperator_graph_iff_inverse (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) (x y : CoeffPair p) :
    (x,y) ∈ (sourceUnboundedOperator hp φ).graph ↔
      sourceDomainInclusion (sourceResolventToDomain hp φ z (z • x-y)) = x := by
  rw [mem_sourceUnboundedOperator_graph]
  constructor
  · rintro ⟨f,rfl,rfl⟩
    have he : z • sourceDomainInclusion f - sourceOperator hp φ f =
        sourceSpectralPencil hp φ z f := by rw [sourceSpectralPencil_eq]; rfl
    rw [he,sourceResolventToDomain_sourceSpectralPencil hp φ z hz]
  · intro h
    refine ⟨sourceResolventToDomain hp φ z (z • x-y),h,?_⟩
    have hi := sourceSpectralPencil_sourceResolventToDomain hp φ z hz (z • x-y)
    rw [sourceSpectralPencil_eq] at hi
    change z • sourceDomainInclusion (sourceResolventToDomain hp φ z (z • x-y)) -
      sourceOperator hp φ (sourceResolventToDomain hp φ z (z • x-y)) = z • x-y at hi
    rw [h] at hi
    exact sub_right_inj.mp hi

/-- Closedness on the full original domain, for every finite Banach exponent and potential. -/
theorem sourceUnboundedOperator_isClosed (hp : p ≠ ⊤) (φ : CoeffPair p) :
    (sourceUnboundedOperator hp φ).IsClosed := by
  obtain ⟨z,hz⟩ := sourceHeightNeumannRegion_nonempty hp φ
  have hr := sourceHeightNeumannRegion_subset_resolventSet hp φ hz
  have he : ((sourceUnboundedOperator hp φ).graph : Set (CoeffPair p × CoeffPair p)) =
      {v | sourceDomainInclusion (sourceResolventToDomain hp φ z (z • v.1-v.2)) = v.1} := by
    ext v
    exact mem_sourceUnboundedOperator_graph_iff_inverse hp φ z hr v.1 v.2
  unfold LinearPMap.IsClosed
  rw [he]
  exact isClosed_eq ((sourceDomainInclusion (p := p)).continuous.comp
    ((sourceResolventToDomain hp φ z).continuous.comp
      ((continuous_fst.const_smul z).sub continuous_snd))) continuous_fst

/-- The potential multiplier has operator norm at most the potential norm. -/
theorem norm_sourcePotentialFromL1_le (φ : CoeffPair p) :
    ‖sourcePotentialFromL1 φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_sourcePotentialFromL1_apply_le φ)

/-- The constant-one square estimate used in the proof of Corollary 3.5, in original norms. -/
theorem norm_sourcePotentialFreeResolvent_sq_le (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2‖ ≤
      ‖φ‖ * ‖sourceDoubleResolvent hp φ z hz‖ := by
  have he : ((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2 =
      (sourcePotentialFromL1 φ).comp (sourceDoubleResolvent hp φ z hz) := by
    rw [sourceDoubleResolvent_eq_comp, pow_two]
    ext a : 1
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sourcePotentialFromL1_le φ) (norm_nonneg _))

/-- The original p-to-one inverse is uniformly small above a common height in both half-planes. -/
theorem exists_sourceFreeResolventToL1_uniform_small (hp : p ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, H ≤ |z.im| → ∀ hz : z ∉ freeLattice,
      ‖sourceFreeResolventToL1 hp z hz‖ < ε := by
  have ht : Filter.Tendsto (fun H : ℝ => CoeffPair.l1Factor p *
      (4*p.toReal/H^(1/p.toReal)+1/H)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_freeL1_heightBound_zero hp).const_mul (CoeffPair.l1Factor p)
  obtain ⟨H,hH,hsmall⟩ := ((Filter.eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_lt_const hε)).exists
  refine ⟨H,hH,?_⟩
  intro z hzi hz
  have him : z.im ≠ 0 := abs_pos.mp (hH.trans_le hzi)
  apply (norm_sourceFreeResolventToL1_le_height hp z hz him).trans_lt
  apply lt_of_le_of_lt ?_ hsmall
  have hfactor := (CoeffPair.l1Factor_pos p).le
  gcongr

/-- The second printed signed coefficient formula; the input first coefficient is reflected. -/
theorem sourceDoubleResolvent_signed_snd_apply (hp : p ≠ ⊤) (φ f : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice) (l : ℤ) :
    (sourceDoubleResolvent hp φ z hz f).snd l =
      ∑' m : ℤ, φ.snd (l+m)*f.fst (-m) /
        ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m)) := by
  rw [sourceDoubleResolvent_snd_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => φ.snd (l-k)*f.fst k /
      ((z-(Real.pi : ℂ)*l)*(z+(Real.pi : ℂ)*k)))]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply, Int.cast_neg, mul_neg, sub_eq_add_neg, neg_neg]

end NLS.ZakharovShabat
