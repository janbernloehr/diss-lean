import NLS.ZakharovShabat.HeightResolvent
import NLS.ZakharovShabat.SourceResolvent

/-! # Infinitesimal relative bounds in the original source norms

The unnumbered Section 3 paragraph on p.23 asserts that potential
multiplication has free-operator relative bound zero. The actual free
resolvent decay proves this uniformly on bounded potential sets, before
transport through the exact original component-sum norm comparison.
Both graph directions retain the actual original one-derivative domain.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The potential has arbitrarily small free-operator relative bound,
uniformly on every bounded potential set. -/
theorem exists_uniform_potential_relative_bound (hp : p ≠ ⊤) (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : PairSpace p, ‖φ‖ ≤ B → ∀ f : Domain p,
      ‖potentialOperator hp φ f‖ ≤ ε*‖freeOperator f‖ + C*‖domainInclusion f‖ := by
  have ht : Tendsto (fun H : ℝ =>
      (4*p.toReal/H^(1/p.toReal)+1/H)*B) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_freeL1_heightBound_zero hp).mul_const B
  obtain ⟨H,hH,hs⟩ := ((eventually_gt_atTop (0:ℝ)).and (ht.eventually_lt_const hε)).exists
  let z : ℂ := (H:ℂ)*Complex.I
  have him : z.im ≠ 0 := by simpa [z] using hH.ne'
  have hz := notMem_freeLattice_of_im_ne_zero him
  refine ⟨1+ε*‖z‖,by positivity,?_⟩
  intro φ hφ f
  have hk : ‖potentialFreeResolvent hp φ z hz‖ ≤ ε := by
    apply (norm_potentialFreeResolvent_le hp φ z hz).trans
    have hb := freeL1Bound_le_height (p := p) hp z hz him
    have hb' : freeL1Bound p hp z hz ≤ 4*p.toReal/H^(1/p.toReal)+1/H := by
      simpa only [z,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
        Complex.ofReal_im,Complex.I_re,mul_zero,add_zero,abs_of_pos hH,one_div] using hb
    exact (mul_le_mul hb' hφ (norm_nonneg _) (by positivity)).trans hs.le
  have he : potentialFreeResolvent hp φ z hz (freePencil z f) = potentialOperator hp φ f := by
    change potentialOperator hp φ (freeResolventToDomain z hz (freePencil z f)) = _
    rw [freeResolventToDomain_freePencil]
  calc
    _ = ‖potentialFreeResolvent hp φ z hz (freePencil z f)‖ := congrArg norm he.symm
    _ ≤ ε*‖freePencil z f‖ :=
      ((potentialFreeResolvent hp φ z hz).le_opNorm _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
    _ ≤ ε*(‖z‖*‖domainInclusion f‖+‖freeOperator f‖) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      simpa only [freePencil,sub_apply,smul_apply,norm_smul]
        using norm_sub_le (z • domainInclusion f) (freeOperator f)
    _ ≤ ε*‖freeOperator f‖+(1+ε*‖z‖)*‖domainInclusion f‖ := by nlinarith [norm_nonneg (domainInclusion f)]

/-- The same infinitesimal bound in both original component-sum norms. -/
theorem exists_uniform_source_potential_relative_bound (hp : p ≠ ⊤)
    (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : CoeffPair p, ‖φ‖ ≤ B →
      ∀ f : WeightedCoeffPair (Weight.sobolev 1) p,
        ‖sourceOperator hp φ f-sourceOperator hp 0 f‖ ≤
          ε*‖sourceOperator hp 0 f‖+C*‖sourceDomainInclusion f‖ := by
  let K : ℝ := 2^(1/p.toReal)
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C,hC,hbound⟩ := exists_uniform_potential_relative_bound hp B (ε/K) (div_pos hε hK)
  refine ⟨K*C,mul_pos hK hC,?_⟩
  intro φ hφ f
  let g : Domain p := WeightedCoeffPair.toMax (Weight.sobolev 1) p f
  have he : sourceOperator hp φ f-sourceOperator hp 0 f =
      (CoeffPair.toMax p).symm (potentialOperator hp (CoeffPair.toMax p φ) g) := by
    change (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ) g)-
      (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p 0) g) = _
    rw [map_zero,operator_zero,← map_sub]
    congr 1
    change freeOperator g+potentialOperator hp (CoeffPair.toMax p φ) g-freeOperator g = _
    abel
  have hf : freeOperator g = CoeffPair.toMax p (sourceOperator hp 0 f) := by
    change freeOperator g = CoeffPair.toMax p
      ((CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p 0) g))
    rw [ContinuousLinearEquiv.apply_symm_apply,map_zero,operator_zero]
  have hi : domainInclusion g = CoeffPair.toMax p (sourceDomainInclusion f) := by
    change domainInclusion g = CoeffPair.toMax p ((CoeffPair.toMax p).symm (domainInclusion g))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [he]
  calc
    _ ≤ K*‖potentialOperator hp (CoeffPair.toMax p φ) g‖ := CoeffPair.norm_toMax_symm_le hp _
    _ ≤ K*((ε/K)*‖freeOperator g‖+C*‖domainInclusion g‖) :=
      mul_le_mul_of_nonneg_left (hbound _ ((CoeffPair.norm_toMax_le φ).trans hφ) g) hK.le
    _ ≤ K*((ε/K)*‖sourceOperator hp 0 f‖+C*‖sourceDomainInclusion f‖) := by
      rw [hf,hi]
      gcongr
      · exact CoeffPair.norm_toMax_le _
      · exact CoeffPair.norm_toMax_le _
    _ = _ := by field_simp

/-- The unnumbered Section 3 claim: each potential has free relative bound zero. -/
theorem exists_source_potential_relative_bound (hp : p ≠ ⊤) (φ : CoeffPair p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : WeightedCoeffPair (Weight.sobolev 1) p,
      ‖sourceOperator hp φ f-sourceOperator hp 0 f‖ ≤
        ε*‖sourceOperator hp 0 f‖+C*‖sourceDomainInclusion f‖ := by
  obtain ⟨C,hC,h⟩ := exists_uniform_source_potential_relative_bound hp ‖φ‖ ε hε
  exact ⟨C,hC,h φ le_rfl⟩

/-- Free and perturbed graph norms compare uniformly on bounded potential sets. -/
theorem exists_uniform_source_graph_comparison (hp : p ≠ ⊤) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : CoeffPair p, ‖φ‖ ≤ B →
      ∀ f : WeightedCoeffPair (Weight.sobolev 1) p,
        (‖sourceOperator hp φ f‖ ≤ 2*‖sourceOperator hp 0 f‖+C*‖sourceDomainInclusion f‖) ∧
        (‖sourceOperator hp 0 f‖ ≤ 2*‖sourceOperator hp φ f‖+C*‖sourceDomainInclusion f‖) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_source_potential_relative_bound hp B (1/2) (by norm_num)
  refine ⟨2*C,by positivity,?_⟩
  intro φ hφ f
  have h := hbound φ hφ f
  have hup := norm_add_le (sourceOperator hp φ f-sourceOperator hp 0 f) (sourceOperator hp 0 f)
  rw [sub_add_cancel] at hup
  have hdown := norm_sub_le (sourceOperator hp φ f) (sourceOperator hp φ f-sourceOperator hp 0 f)
  rw [sub_sub_cancel] at hdown
  constructor <;> nlinarith [norm_nonneg (sourceOperator hp 0 f),
    norm_nonneg (sourceOperator hp φ f), mul_nonneg hC.le (norm_nonneg (sourceDomainInclusion f))]

end NLS.ZakharovShabat
