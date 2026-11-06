import NLS.KdV.HillAbelianCoordinateSequence
import NLS.SequenceSpaces.HilbertCoordinateContinuity

/-! # Native weighted norm continuity of the actual Abelian coordinate map -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem continuous_hillAbelianPositiveCoefficient (w : SpectralWeight) (n : ℕ) :
    Continuous (fun p : RealHillWeightedPotential w => hillAbelianPositiveCoefficient w p n) := by
  by_cases hn : 1≤n
  · simpa only [hillAbelianPositiveCoefficient,dif_pos hn,Function.comp_def] using
      (continuous_hillDirichletAbelianCoordinate h0q h0r n hn).comp (continuous_hillRealWeightedEmbedding w)
  · simp only [hillAbelianPositiveCoefficient,dif_neg hn]
    exact continuous_const

theorem continuous_hillAbelianRawCoordinateSequence (w : SpectralWeight) (k : ℤ) :
    Continuous (fun p : RealHillWeightedPotential w => hillAbelianRawCoordinateSequence w p k) := by
  unfold hillAbelianRawCoordinateSequence
  split_ifs
  · exact continuous_hillAbelianPositiveCoefficient h0q h0r w k.natAbs
  · exact (continuous_hillAbelianPositiveCoefficient h0q h0r w k.natAbs).star

omit h0q h0r in
/-- The positive weighted squared amplitudes, with the zero mode included. -/
def hillAbelianWeightedAmplitude (w : SpectralWeight) (p : RealHillWeightedPotential w) (n : ℕ) : ℝ :=
  ‖(hillAbelianTargetWeight w (n:ℤ):ℂ)*hillAbelianRawCoordinateSequence w p (n:ℤ)‖^2

theorem summable_hillAbelianWeightedAmplitude (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Summable (hillAbelianWeightedAmplitude w p) := by
  have hs : Summable (fun k : ℤ => ‖(hillAbelianTargetWeight w k:ℂ)*hillAbelianRawCoordinateSequence w p k‖^2) := by
    have hm := (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mp
      (memlp_hillAbelianRawCoordinateSequence h0q h0r w p)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hm
  exact hs.comp_injective (show Function.Injective (fun n : ℕ => (n:ℤ)) from Nat.cast_injective)

omit h0q h0r in
theorem hillAbelianWeightedAmplitude_zero (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    hillAbelianWeightedAmplitude w p 0=0 := by simp [hillAbelianWeightedAmplitude]

theorem hillAbelianWeightedAmplitude_le_actionTerm (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) (hn : 1≤n) :
    hillAbelianWeightedAmplitude w p n≤(1/Real.pi)*hillWeightedActionTerm w p n := by
  rw [hillAbelianWeightedAmplitude,hillAbelian_weighted_norm_sq_nat h0q h0r w p n hn]
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hI := hillPeriodOneAction_nonneg w p.val p.property n hn
  calc
    _ = (1+(n:ℝ))*(w (2*(n:ℤ))^2*hillPeriodOneAction w p.val p.property n) := by ring
    _ ≤ (2*(n:ℝ))*(w (2*(n:ℤ))^2*hillPeriodOneAction w p.val p.property n) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg _) hI)
    _ = _ := by dsimp only [hillWeightedActionTerm]; field_simp

/-- The full positive squared amplitude sum is continuous, using uniform
physical action tails rather than a coordinatewise convergence argument. -/
theorem continuous_tsum_hillAbelianWeightedAmplitude (w : SpectralWeight) :
    Continuous (fun p : RealHillWeightedPotential w => ∑' n : ℕ, hillAbelianWeightedAmplitude w p n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply continuousAt_tsum_of_locally_small_nat_tails (hillAbelianWeightedAmplitude w) q
    (summable_hillAbelianWeightedAmplitude h0q h0r w)
    (fun n => (((continuous_hillAbelianRawCoordinateSequence h0q h0r w (n:ℤ)).const_mul _).norm.pow 2).continuousAt)
  intro ε hε
  obtain ⟨N,U,hN,hU,hqU,ht⟩ := exists_hillWeightedActionTerm_small_tail w q (ε*Real.pi) (mul_pos hε Real.pi_pos)
  refine ⟨N, ?_⟩
  filter_upwards [hU.mem_nhds hqU] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun n => sq_nonneg _))]
  have hs := (summable_nat_add_iff N).mpr (summable_hillAbelianWeightedAmplitude h0q h0r w p)
  calc
    _ ≤ ∑' j : ℕ, (1/Real.pi)*hillWeightedActionTerm w p (j+N) :=
      hs.tsum_le_tsum (fun j => hillAbelianWeightedAmplitude_le_actionTerm h0q h0r w p (j+N) (by omega))
        ((ht p hp).1.mul_left _)
    _ = (1/Real.pi)*(∑' j : ℕ, hillWeightedActionTerm w p (j+N)) := tsum_mul_left
    _ ≤ (1/Real.pi)*(ε*Real.pi) := mul_le_mul_of_nonneg_left (ht p hp).2 (by positivity)
    _ = ε := by field_simp

/-- Exact Parseval identity for the literal signed physical coordinates. -/
theorem norm_sq_hillAbelianCoordinateSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    ‖hillAbelianCoordinateSequence h0q h0r w p‖^2 = 2*(∑' n : ℕ, hillAbelianWeightedAmplitude w p n) := by
  rw [WeightedCoeff.norm_eq]
  apply Coeff.norm_sq_eq_twice_tsum_nat
  · simp only [WeightedCoeff.weightEquiv_apply,hillAbelianCoordinateSequence_apply,
      hillAbelianRawCoordinateSequence_zero,mul_zero]
  · intro k
    have he := hillAbelian_weighted_norm_sq_neg w p k
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- The actual Abelian map is continuous in the full weighted half-shift
norm, at every real source including arbitrary closed gaps. -/
theorem continuous_hillAbelianCoordinateSequence (w : SpectralWeight) :
    Continuous (hillAbelianCoordinateSequence h0q h0r w) := by
  let a : RealHillWeightedPotential w → Coeff 2 := fun p =>
    WeightedCoeff.weightEquiv (hillAbelianTargetWeight w) 2 (hillAbelianCoordinateSequence h0q h0r w p)
  have hc : Continuous a := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply Coeff.continuousAt_of_coordinatewise_of_norm_sq a p
    · intro k
      exact ((continuous_hillAbelianRawCoordinateSequence h0q h0r w k).const_mul _).continuousAt
    · have he : (fun p => ‖a p‖^2) = (fun p => 2*(∑' n : ℕ, hillAbelianWeightedAmplitude w p n)) := by
        funext p
        exact norm_sq_hillAbelianCoordinateSequence h0q h0r w p
      rw [he]
      exact ((continuous_tsum_hillAbelianWeightedAmplitude h0q h0r w).const_mul 2).continuousAt
  have h := (WeightedCoeff.weightIsometry (hillAbelianTargetWeight w) 2).symm.continuous.comp hc
  change Continuous (fun p => (WeightedCoeff.weightIsometry (hillAbelianTargetWeight w) 2).symm
    ((WeightedCoeff.weightIsometry (hillAbelianTargetWeight w) 2) (hillAbelianCoordinateSequence h0q h0r w p))) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

omit h0q h0r in
private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _

omit h0q h0r in
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

omit h0q h0r in
/-- The literal physical Abelian map on the entire real weighted source.
Global canonicality, bijectivity and Banach analyticity remain separate
obligations; this definition supplies none of them as hypotheses. -/
def hillPhysicalAbelianMap (w : SpectralWeight) :
    RealHillWeightedPotential w → WeightedCoeff (hillAbelianTargetWeight w) 2 :=
  hillAbelianCoordinateSequence zero_parity zero_real w

omit h0q h0r in
theorem continuous_hillPhysicalAbelianMap (w : SpectralWeight) :
    Continuous (hillPhysicalAbelianMap w) :=
  continuous_hillAbelianCoordinateSequence zero_parity zero_real w

omit h0q h0r in
theorem hillPhysicalAbelianMap_real (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    (hillPhysicalAbelianMap w p).val 0=0 ∧
      ∀ k : ℤ, (hillPhysicalAbelianMap w p).val (-k)=conj ((hillPhysicalAbelianMap w p).val k) :=
  hillAbelianCoordinateSequence_real zero_parity zero_real w p

omit h0q h0r in
theorem hillPhysicalAbelianMap_action (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) (hn : 1≤n) :
    (hillPhysicalAbelianMap w p).val (n:ℤ)*(hillPhysicalAbelianMap w p).val (-(n:ℤ))=
      (hillPeriodOneAction w p.val p.property n:ℂ) :=
  hillAbelianCoordinateSequence_action zero_parity zero_real w p n hn

end NLS.KdV
