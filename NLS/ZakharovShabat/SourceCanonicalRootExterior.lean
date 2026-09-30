import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.StandardRootGapCorrectionExterior
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles
import NLS.ZakharovShabat.CentralCircleThresholds

/-!
# Exterior normalization of the actual canonical root

The literal symmetric canonical-root cutoffs factor into the midpoint
single product and the principal-square-root gap corrections. Absolute
convergence identifies this factorization with the actual canonical root.
The resulting ratio to `-2i sin z` tends to one outside fixed free discs,
uniformly on the large circles used in Lemma 12.11.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite canonical-root product separates the midpoint product and
the actual principal-square-root corrections, with the correct factor `i`. -/
theorem sourceCanonicalRootPartialProduct_eq_midpoint_mul_correction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (N : ℕ) :
    sourceCanonicalRootPartialProduct hp hp1 N ψ z =
      I * singleSpectralPartialProduct
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z N *
      ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        standardRootGapCorrection
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z m := by
  have he (m : ℤ) : sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m =
      singleSpectralFactor
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z m *
      standardRootGapCorrection
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z m := by
    unfold sourceStandardRoot normalizedStandardRoot singleSpectralFactor
      standardRootGapCorrection spectralGapRadicand
    ring
  simp only [sourceCanonicalRootPartialProduct, he, Finset.prod_mul_distrib,
    singleSpectralPartialProduct]
  ring

/-- Absolute convergence of the square-root corrections identifies their
product with the actual canonical root, rather than an independently
chosen square root of the discriminant. -/
theorem sourceCanonicalRoot_eq_midpoint_mul_correction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hs : Summable (fun m : ℤ => ‖standardRootGapCorrection
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z m-1‖)) :
    sourceCanonicalRoot hp hp1 ψ z =
      I * entireSingleSpectralProduct
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z *
      ∏' m, standardRootGapCorrection
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z m := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hτ : Memℓp (fun m => τ m-(Real.pi : ℂ)*m) p := by
    have he : (sourcePeriodicMidpointDisplacement hp hp1 ψ : ℤ → ℂ) =
        fun m => τ m-(Real.pi : ℂ)*m := by
      funext m
      exact sourcePeriodicMidpointDisplacement_apply hp hp1 ψ m
    rw [← he]
    exact lp.memℓp _
  have hlinear := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp τ hτ).tendsto_at
    (mem_univ z)
  have hcorr : Tendsto (fun N : ℕ =>
      ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), standardRootGapCorrection τ γ z m)
      atTop (𝓝 (∏' m, standardRootGapCorrection τ γ z m)) := by
    have h := (multipliable_one_add_of_summable hs).hasProd.comp Finset.tendsto_Icc_neg
    simpa only [add_sub_cancel, Function.comp_def, τ, γ] using h
  have hprod := (hlinear.const_mul I).mul hcorr
  apply tendsto_nhds_unique (tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z)
  exact hprod.congr' (Eventually.of_forall (fun N =>
    (sourceCanonicalRootPartialProduct_eq_midpoint_mul_correction hp hp1 ψ z N).symm))

/-- The actual canonical root has the free normalization at infinity
along every path separated from the free lattice by a fixed radius. -/
theorem tendsto_sourceCanonicalRoot_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    Tendsto (fun i => sourceCanonicalRoot hp hp1 ψ (z i) / (-2*I*sin (z i))) l (𝓝 1) := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hτ : Memℓp (fun m => τ m-(Real.pi : ℂ)*m) p := by
    have he : (sourcePeriodicMidpointDisplacement hp hp1 ψ : ℤ → ℂ) =
        fun m => τ m-(Real.pi : ℂ)*m := by
      funext m
      exact sourcePeriodicMidpointDisplacement_apply hp hp1 ψ m
    rw [← he]
    exact lp.memℓp _
  have hγ : Memℓp γ p := by
    have he : (sourcePeriodicGapDisplacement hp hp1 ψ : ℤ → ℂ) = γ := by
      funext m
      exact sourcePeriodicGapDisplacement_apply hp hp1 ψ m
    rw [← he]
    exact lp.memℓp _
  obtain ⟨hs, ht⟩ := standardRootGapCorrection_exterior_limit hp τ γ hτ hγ z hescape hr hrπ hsep
  have hmid := tendsto_entireSingleSpectralProduct_div_free_of_separated hp τ hτ z hescape hr hrπ hsep
  have hprod : Tendsto (fun i =>
      (entireSingleSpectralProduct τ (z i)/(-2*sin (z i))) *
        ∏' m, standardRootGapCorrection τ γ (z i) m) l (𝓝 1) := by
    simpa only [mul_one] using hmid.mul ht
  apply hprod.congr'
  filter_upwards [hs] with i hi
  rw [sourceCanonicalRoot_eq_midpoint_mul_correction hp hp1 ψ (z i) hi]
  have hsin := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated hr (hsep i))
  field_simp
  rfl

/-- Every sufficiently distant separated point avoids every closed gap.
Both endpoints lie in a free-centered closed ball of half the distance
to the spectral point; convexity encloses their whole straight segment. -/
theorem eventually_sourceCanonicalRootDomain_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    ∀ᶠ i in l, z i ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hspec := (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ)).1
  have ha := eventually_midpoint_relative_norm_le_half_of_separated hp a
    hspec.left_displacement z hescape hr hrπ hsep
  have hb := eventually_midpoint_relative_norm_le_half_of_separated hp b
    hspec.right_displacement z hescape hr hrπ hsep
  filter_upwards [ha, hb] with i hi hj m hmem
  have hd : 0 < ‖z i-(Real.pi : ℂ)*m‖ := lt_of_lt_of_le hr (hsep i m)
  have hleft : a m ∈ closedBall ((Real.pi : ℂ)*m) (‖z i-(Real.pi : ℂ)*m‖/2) := by
    rw [mem_closedBall, dist_eq_norm]
    have h := hi m
    rw [norm_div] at h
    have h := (div_le_iff₀ hd).mp h
    linarith
  have hright : b m ∈ closedBall ((Real.pi : ℂ)*m) (‖z i-(Real.pi : ℂ)*m‖/2) := by
    rw [mem_closedBall, dist_eq_norm]
    have h := hj m
    rw [norm_div] at h
    have h := (div_le_iff₀ hd).mp h
    linarith
  have hball := (convex_closedBall ((Real.pi : ℂ)*m)
    (‖z i-(Real.pi : ℂ)*m‖/2)).segment_subset hleft hright hmem
  rw [mem_closedBall, dist_eq_norm] at hball
  linarith

/-- The large half-integer circles eventually lie entirely in the
actual complement of all closed periodic gaps. -/
theorem eventually_centralCircle_sourceCanonicalRootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∀ᶠ k : ℕ in atTop,
      sphere (0 : ℂ) (centralCircleRadius k) ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  let S := {z : ℂ // ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖}
  have hdom := eventually_sourceCanonicalRootDomain_of_separated hp hp1 ψ
    (fun z : S => z.val) tendsto_comap (by positivity : 0 < Real.pi/4) le_rfl
    (fun z => z.property)
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop (fun z : S => ‖z.val‖) hdom
  apply eventually_centralCircle_of_separated_threshold
  exact ⟨R, fun z hz hsep => hR ⟨z,hsep⟩ hz⟩

/-- One threshold controls the actual canonical-root/free-sine error at
every separated spectral point of sufficiently large norm. -/
theorem exists_threshold_sourceCanonicalRoot_div_free_close
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi : ℂ)*m‖) →
      ‖sourceCanonicalRoot hp hp1 ψ z / (-2*I*sin z)-1‖ ≤ ε := by
  let S := {z : ℂ // ∀ m : ℤ, r ≤ ‖z-(Real.pi : ℂ)*m‖}
  have ht := tendsto_sourceCanonicalRoot_div_free_of_separated
    hp hp1 ψ (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property)
  have hn := (ht.sub_const 1).norm
  simp only [sub_self, norm_zero] at hn
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop
    (fun z : S => ‖z.val‖) (hn.eventually (gt_mem_nhds hε))
  exact ⟨R, fun z hz hsep => (hR ⟨z,hsep⟩ hz).le⟩

/-- The canonical-root ratio tends uniformly to one on the half-integer
large circles of Lemma 12.11. -/
theorem eventually_centralCircle_sourceCanonicalRoot_div_free_close
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      ‖sourceCanonicalRoot hp hp1 ψ z / (-2*I*sin z)-1‖ ≤ ε := by
  obtain ⟨R, hR⟩ := exists_threshold_sourceCanonicalRoot_div_free_close
    hp hp1 ψ (by positivity : 0 < Real.pi/4) le_rfl hε
  obtain ⟨K, hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K, ?_⟩
  intro k hk z hz
  have hK : R < (K : ℝ)*Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere, dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hRk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

/-- All sufficiently large half-integer circles are zero-free for the
actual canonical root. -/
theorem eventually_centralCircle_sourceCanonicalRoot_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      sourceCanonicalRoot hp hp1 ψ z ≠ 0 := by
  obtain ⟨K, hK⟩ := eventually_centralCircle_sourceCanonicalRoot_div_free_close
    hp hp1 ψ (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨K, ?_⟩
  intro k hk z hz hzero
  have hbound := hK k hk z hz
  rw [hzero, zero_div, zero_sub, norm_neg, norm_one] at hbound
  norm_num at hbound

end NLS.ZakharovShabat
