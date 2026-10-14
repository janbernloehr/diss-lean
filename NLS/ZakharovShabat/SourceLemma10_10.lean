import NLS.ZakharovShabat.SourceCriticalGapCommonAnalytic
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.ZakharovShabat.SourceLemma10_8Estimates

/-!
# Lemma 10.10 on the unchanged common source domain

Every critical root is its midpoint plus the squared gap times the actual
analytic quotient. A finite central block and the uniform distant-root
estimate give one local lp bound at every source in W. No division by a
gap, reality assumption on the nearby source, or index cutoff is needed.
The preceding Section 10 data and its common domain are retained.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The central analytic coordinates and uniform tail give one local full-sequence bound. -/
theorem SourceLemma10_5Data.uniform_criticalGapQuotient
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ V, ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ K := by
  obtain ⟨N,_,U,hUopen,_,hφU,_,K,hK,htail⟩ :=
    exists_uniform_critical_midpoint_gap_sq_lp hp hp1 (periodOnePotential φ)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨V₀,hV₀open,hφV₀,B,hB,hcentral⟩ :=
    h.uniform_criticalGapQuotient_finiteBlock φ hφ s
  let T : Set (CoeffPair p) := (periodOnePotential ⁻¹' U) ∩ V₀ ∩ W
  have hTopen : IsOpen T :=
    ((hUopen.preimage (periodOnePotential (p := p)).continuous).inter hV₀open).inter hW
  have hφT : φ ∈ T := ⟨⟨hφU,hφV₀⟩,hφ⟩
  obtain ⟨r,hr,hrT⟩ := Metric.mem_nhds_iff.mp (hTopen.mem_nhds hφT)
  refine ⟨ball φ r,isOpen_ball,isConnected_ball hr,mem_ball_self hr,
    fun ψ hψ => (hrT hψ).2,s.card*B+K+1,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨⟨hψU,hψV₀⟩,_⟩ := hrT hψ
  obtain ⟨a,ha,hatail⟩ := htail (periodOnePotential ψ) hψU (periodOnePotential_mem ψ)
  have hnorm : ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ s.card*B+K := by
    apply (NLS.Coeff.norm_le_of_eq_outside_finset
      (sourceCriticalGapQuotient hp hp1 ψ) a s B
      (fun n hn => hcentral ψ hψV₀ n hn) (fun n hn => ?_)).trans
        (add_le_add le_rfl ha)
    exact (hatail n (by simp only [s,Finset.mem_Icc] at hn; omega)).1.symm
  linarith

/-- Lemma 10.10 with actual coefficients, all indices, and original-topology local uniformity. -/
structure SourceLemma10_10Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_8Estimates hp hp1 W
  coefficient_nonzero : ∀ ψ ∈ W, ∀ n : ℤ,
    canonicalCriticalOffsetCoefficient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0
  exact_offset : ∀ ψ ∈ W, ∀ n : ℤ,
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceCriticalGapQuotient hp hp1 ψ n
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (fun ψ => sourceCriticalGapQuotient hp hp1 ψ n) W
  locally_uniform : ∀ φ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ V, ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ K

/-- Lemma 10.10 strengthens the existing common-domain package without shrinking W. -/
theorem SourceLemma10_8Estimates.criticalOffsets
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_8Estimates hp hp1 W) (hW : IsOpen W) : SourceLemma10_10Data hp hp1 W := by
  have h5 := h.previous.previous.roots
  have hnonzero (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
      canonicalCriticalOffsetCoefficient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 := by
    obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := h5.neighborhoods ψ hψ
    exact hD.toSourceIsolatingNeighborhoods.criticalOffsetCoefficient_ne_zero ψ hψV n
  refine ⟨h,hnonzero,?_,fun n ψ hψ => h5.analyticAt_criticalGapQuotient ψ hψ n,
    h5.uniform_criticalGapQuotient hW⟩
  intro ψ hψ n
  have he := canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n (hnonzero ψ hψ n)
  simp only [canonicalCriticalMidpointOffset_apply] at he
  change _ = _ + _
  rw [sourceCriticalGapQuotient_apply,sourcePeriodicGapDisplacement_apply,
    canonicalCriticalGapQuotient]
  linear_combination he

/-- The literal coefficient power sum is locally bounded on the same common domain. -/
theorem SourceLemma10_10Data.locally_uniform_powerSum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_10Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ V,
        (∑' n : ℤ, ‖sourceCriticalGapQuotient hp hp1 ψ n‖^p.toReal) ≤ K := by
  obtain ⟨V,ho,hc,hφV,hVW,K,hK,hbound⟩ := h.locally_uniform φ hφ
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (lt_trans zero_lt_one hp1).ne' hp
  refine ⟨V,ho,hc,hφV,hVW,K^p.toReal,Real.rpow_pos_of_pos hK _,?_⟩
  intro ψ hψ
  rw [← lp.norm_rpow_eq_tsum hpR]
  exact Real.rpow_le_rpow (norm_nonneg _) (hbound ψ hψ) hpR.le

/-- A collapsed gap has its critical point at the midpoint, including in the central block. -/
theorem SourceLemma10_10Data.critical_eq_midpoint_of_gap_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_10Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  simpa only [hgap,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,add_zero] using h.exact_offset ψ hψ n

/-- Lemma 10.10 for every finite p>1, retaining the preceding common-domain data. -/
theorem sourceLemma10_10 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_10Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_8_estimates hp hp1
  exact ⟨W,ho,hc,hr,h.criticalOffsets ho⟩

end NLS.ZakharovShabat
