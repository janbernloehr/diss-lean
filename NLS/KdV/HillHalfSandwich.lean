import NLS.KdV.HillHalfSandwichSquareSum
import NLS.KdV.HillHalfDenominatorPhysical

/-! The actual source normalized perturbation S_lambda on ALL l2 and
physical periodic L2 inputs, with its proved rough-potential norm bound. -/
noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier

/-- A proof-independent actual l2 operator family. Source-circle hypotheses
recover every original matrix entry from the proved squared-entry summability. -/
def hillHalfSandwich (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) :
    Coeff 2 →L[ℂ] Coeff 2 :=
  if hM : Summable (fun p : ℤ × ℤ => ‖hillHalfSandwichMatrix r q z p.1 p.2‖^2) then
    Coeff.squareSummableMatrixCLM (hillHalfSandwichMatrix r q z) hM else 0

/-- The source-circle family is EXACTLY the actual full squared-summable matrix. -/
theorem hillHalfSandwich_eq_matrix (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    hillHalfSandwich r q z = Coeff.squareSummableMatrixCLM (hillHalfSandwichMatrix r q z)
      (summable_hillHalfSandwichMatrix_sq r hr hr1 q n hn hlog z hz) := by
  rw [hillHalfSandwich,dif_pos (summable_hillHalfSandwichMatrix_sq r hr hr1 q n hn hlog z hz)]

/-- Every output is the genuine absolutely convergent source matrix row sum. -/
theorem hillHalfSandwich_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (x : Coeff 2) (l : ℤ) :
    hillHalfSandwich r q z x l = ∑' m : ℤ,
      q.val (l-m)*hillHalfDenominatorRaw z l*hillHalfDenominatorRaw z m*x m := by
  rw [hillHalfSandwich_eq_matrix r hr hr1 q n hn hlog z hz,Coeff.squareSummableMatrixCLM_apply]
  rfl

/-- The ACTUAL full l2 operator has the rough-potential high-energy bound,
without a supplied bounded-operator or matrix-summability assumption. -/
theorem norm_sq_hillHalfSandwich_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfSandwich r q z‖^2 ≤
      (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2))*‖q‖^2 := by
  rw [hillHalfSandwich_eq_matrix r hr hr1 q n hn hlog z hz]
  exact (Coeff.norm_sq_squareSummableMatrixCLM_le _ _).trans
    (tsum_hillHalfSandwichMatrix_sq_le r hr hr1 q n hn hlog z hz)

/-- S_lambda on the ENTIRE source-normalized physical periodic L2 space. -/
def hillPhysicalHalfSandwich (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) :
    CircleL2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hillHalfSandwich r q z).comp l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Physical realization preserves the exact actual coefficient operator norm. -/
theorem norm_hillPhysicalHalfSandwich (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) :
    ‖hillPhysicalHalfSandwich r q z‖ = ‖hillHalfSandwich r q z‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro F
    change ‖l2Synthesis (hillHalfSandwich r q z (l2Synthesis.symm F))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (hillHalfSandwich r q z).le_of_opNorm_le le_rfl _ |>.trans_eq
      (by rw [LinearIsometryEquiv.norm_map])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (hillPhysicalHalfSandwich r q z).le_opNorm (l2Synthesis x)
    change ‖l2Synthesis (hillHalfSandwich r q z (l2Synthesis.symm (l2Synthesis x)))‖ ≤ _ at h
    simpa only [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.norm_map] using h

/-- The FULL physical Fourier action is the actual original normalized source row sum. -/
theorem hillPhysicalHalfSandwich_coefficient (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (F : CircleL2) (l : ℤ) :
    fourierCoeff (hillPhysicalHalfSandwich r q z F) l = ∑' m : ℤ,
      q.val (l-m)*hillHalfDenominatorRaw z l*hillHalfDenominatorRaw z m*fourierCoeff F m := by
  change fourierCoeff (l2Synthesis (hillHalfSandwich r q z (l2Synthesis.symm F))) l = _
  rw [fourierCoeff_l2Synthesis,hillHalfSandwich_apply r hr hr1 q n hn hlog z hz]
  apply tsum_congr
  intro m
  rw [← fourierBasis_repr]
  rfl

/-- The original physical L2 norm has the SAME quantitative high-energy estimate. -/
theorem norm_sq_hillPhysicalHalfSandwich_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillPhysicalHalfSandwich r q z‖^2 ≤
      (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2))*‖q‖^2 := by
  rw [norm_hillPhysicalHalfSandwich]
  exact norm_sq_hillHalfSandwich_le r hr hr1 q n hn hlog z hz

end NLS.KdV
