import NLS.KdV.HillAbelianCoordinateAnalytic
import NLS.KdV.HillWeightedActionContinuity
import NLS.SequenceSpaces.WeightedHilbertProduct
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The actual signed Abelian coordinate sequence in its weighted half-shift -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The source weight with the Birkhoff half-derivative shift, retaining
the actual period-one doubled-index convention. -/
def hillAbelianTargetWeight (w : SpectralWeight) : Weight :=
  w.doubleIndex.toWeight.product (Weight.sobolev (1/2))

def hillAbelianPositiveCoefficient (w : SpectralWeight) (p : RealHillWeightedPotential w) (n : ℕ) : ℂ :=
  if hn : 1≤n then hillDirichletAbelianCoordinate
    (hillRealWeightedEmbedding w p).val (hillRealWeightedEmbedding w p).property.1
      (hillRealWeightedEmbedding w p).property.2 n hn else 0

@[simp] theorem hillAbelianPositiveCoefficient_zero (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    hillAbelianPositiveCoefficient w p 0=0 := by simp [hillAbelianPositiveCoefficient]

def hillAbelianRawCoordinateSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℤ) : ℂ :=
  if 0≤k then hillAbelianPositiveCoefficient w p k.natAbs else conj (hillAbelianPositiveCoefficient w p k.natAbs)

@[simp] theorem hillAbelianRawCoordinateSequence_zero (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    hillAbelianRawCoordinateSequence w p 0=0 := by simp [hillAbelianRawCoordinateSequence]

theorem hillAbelianRawCoordinateSequence_neg (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℤ) :
    hillAbelianRawCoordinateSequence w p (-k)=conj (hillAbelianRawCoordinateSequence w p k) := by
  by_cases hk : k=0
  · subst k;simp
  by_cases hkp : 0≤k
  · have hn : ¬0≤-k := by omega
    simp only [hillAbelianRawCoordinateSequence,if_neg hn,Int.natAbs_neg,if_pos hkp]
  · have hn : 0≤-k := by omega
    simp only [hillAbelianRawCoordinateSequence,if_pos hn,Int.natAbs_neg,if_neg hkp,conj_conj]

theorem norm_hillAbelianRawCoordinateSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℤ) :
    ‖hillAbelianRawCoordinateSequence w p k‖=‖hillAbelianPositiveCoefficient w p k.natAbs‖ := by
  unfold hillAbelianRawCoordinateSequence
  split_ifs <;> simp only [norm_conj]

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem norm_sq_hillAbelianPositiveCoefficient (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) (hn : 1≤n) :
    ‖hillAbelianPositiveCoefficient w p n‖^2=hillPeriodOneAction w p.val p.property n := by
  rw [hillAbelianPositiveCoefficient,dif_pos hn]
  exact norm_sq_hillDirichletAbelianCoordinate _ _ _ h0q h0r n hn

/-- The squared weighted coefficient at a positive index has exactly the
physical action amplitude; no factor from real Cartesian coordinates occurs. -/
theorem hillAbelian_weighted_norm_sq_nat (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) (hn : 1≤n) :
    ‖(hillAbelianTargetWeight w (n:ℤ):ℂ)*hillAbelianRawCoordinateSequence w p (n:ℤ)‖^2=
      w (2*(n:ℤ))^2*(1+(n:ℝ))*hillPeriodOneAction w p.val p.property n := by
  rw [norm_mul,mul_pow,norm_hillAbelianRawCoordinateSequence,Int.natAbs_natCast,
    norm_sq_hillAbelianPositiveCoefficient h0q h0r w p n hn]
  rw [norm_real,Real.norm_of_nonneg ((hillAbelianTargetWeight w).positive (n:ℤ)).le]
  simp only [hillAbelianTargetWeight,Weight.product_apply,
    SpectralWeight.doubleIndex_apply,Weight.sobolev_apply,Int.cast_natCast,
    mul_pow,← Real.sqrt_eq_rpow]
  rw [abs_of_nonneg (show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n),
    Real.sq_sqrt (by positivity : (0:ℝ)≤1+(n:ℝ))]

omit h0q h0r in
theorem hillAbelian_weighted_norm_sq_neg (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℤ) :
    ‖(hillAbelianTargetWeight w (-k):ℂ)*hillAbelianRawCoordinateSequence w p (-k)‖^2=
      ‖(hillAbelianTargetWeight w k:ℂ)*hillAbelianRawCoordinateSequence w p k‖^2 := by
  have hw : hillAbelianTargetWeight w (-k)=hillAbelianTargetWeight w k := by
    simp only [hillAbelianTargetWeight,Weight.product_apply,
      SpectralWeight.doubleIndex_apply,mul_neg,SpectralWeight.apply_neg,
      Weight.sobolev_apply,Int.cast_neg,abs_neg]
  rw [hw,hillAbelianRawCoordinateSequence_neg,norm_mul,norm_mul,norm_conj]

omit h0q h0r in
/-- The full actual action amplitudes have the weighted half-shift
summability needed for the Birkhoff codomain. -/
theorem summable_hillAbelian_weighted_action_amplitudes (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Summable (fun j : ℕ => w (2*((j+1:ℕ):ℤ))^2*(1+(j+1:ℕ):ℝ)*
      hillPeriodOneAction w p.val p.property (j+1)) := by
  have hs := (summable_hillWeightedActionTerm w p).comp_injective Nat.succ_injective
  apply (hs.mul_left (1/Real.pi)).of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
      (hillPeriodOneAction_nonneg w p.val p.property (j+1) (by omega)))
  intro j
  have hI := hillPeriodOneAction_nonneg w p.val p.property (j+1) (by omega)
  have hn : (1:ℝ)≤(j+1:ℕ) := by exact_mod_cast (show 1≤j+1 by omega)
  calc
    _ = (1+(j+1:ℕ):ℝ)*(w (2*((j+1:ℕ):ℤ))^2*hillPeriodOneAction w p.val p.property (j+1)) := by ring
    _ ≤ (2*(j+1:ℕ):ℝ)*(w (2*((j+1:ℕ):ℤ))^2*hillPeriodOneAction w p.val p.property (j+1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg _) hI)
    _ = _ := by
      dsimp only [Function.comp_def,hillWeightedActionTerm]
      field_simp

/-- Membership is proved for the literal signed physical coordinate
sequence, in its native weighted norm. It is not an abstract target model. -/
theorem memlp_hillAbelianRawCoordinateSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Memℓp (fun k => (hillAbelianTargetWeight w k:ℂ)*hillAbelianRawCoordinateSequence w p k) 2 := by
  let f : ℤ → ℝ := fun k => ‖(hillAbelianTargetWeight w k:ℂ)*hillAbelianRawCoordinateSequence w p k‖^2
  have hs : Summable (fun j : ℕ => f ((j+1:ℕ):ℤ)) := by
    have he : (fun j : ℕ => f ((j+1:ℕ):ℤ)) =
        (fun j : ℕ => w (2*((j+1:ℕ):ℤ))^2*(1+(j+1:ℕ):ℝ)*
          hillPeriodOneAction w p.val p.property (j+1)) := by
      funext j
      exact hillAbelian_weighted_norm_sq_nat h0q h0r w p (j+1) (by omega)
    rw [he]
    exact summable_hillAbelian_weighted_action_amplitudes w p
  have hnat : Summable (fun j : ℕ => f (j:ℤ)) := (summable_nat_add_iff 1).mp hs
  have hneg : Summable (fun j : ℕ => f (-(j:ℤ))) := by
    simpa only [f,hillAbelian_weighted_norm_sq_neg] using hnat
  have hint : Summable f := summable_int_iff_summable_nat_and_neg.mpr ⟨hnat,hneg⟩
  rw [memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hint

/-- The actual signed physical Abelian sequence in the Birkhoff target
with half a derivative gained over the given source weight. -/
def hillAbelianCoordinateSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    WeightedCoeff (hillAbelianTargetWeight w) 2 :=
  ⟨hillAbelianRawCoordinateSequence w p,memlp_hillAbelianRawCoordinateSequence h0q h0r w p⟩

@[simp] theorem hillAbelianCoordinateSequence_apply (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℤ) :
    (hillAbelianCoordinateSequence h0q h0r w p).val k=hillAbelianRawCoordinateSequence w p k := rfl

/-- The zero mode and signed reality conditions of the source sequence. -/
theorem hillAbelianCoordinateSequence_real (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    (hillAbelianCoordinateSequence h0q h0r w p).val 0=0 ∧
      ∀ k : ℤ, (hillAbelianCoordinateSequence h0q h0r w p).val (-k)=
        conj ((hillAbelianCoordinateSequence h0q h0r w p).val k) :=
  ⟨hillAbelianRawCoordinateSequence_zero w p,hillAbelianRawCoordinateSequence_neg w p⟩

/-- The actual signed-coordinate product is precisely the positive action. -/
theorem hillAbelianCoordinateSequence_action (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) (hn : 1≤n) :
    (hillAbelianCoordinateSequence h0q h0r w p).val (n:ℤ)*
      (hillAbelianCoordinateSequence h0q h0r w p).val (-(n:ℤ))=
        (hillPeriodOneAction w p.val p.property n:ℂ) := by
  rw [hillAbelianCoordinateSequence_apply,hillAbelianCoordinateSequence_apply,hillAbelianRawCoordinateSequence_neg]
  rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  have hnrm : ‖hillAbelianRawCoordinateSequence w p (n:ℤ)‖^2=hillPeriodOneAction w p.val p.property n := by
    rw [norm_hillAbelianRawCoordinateSequence,Int.natAbs_natCast,norm_sq_hillAbelianPositiveCoefficient h0q h0r w p n hn]
  exact congrArg (fun x : ℝ => (x:ℂ)) hnrm

end NLS.KdV
