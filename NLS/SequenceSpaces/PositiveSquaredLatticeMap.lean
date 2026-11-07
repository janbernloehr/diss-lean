import NLS.SequenceSpaces.SquaredLatticeDisplacement
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.SequenceSpaces.LpCoordinateContinuity

/-! Squaring a displaced signed lattice is analytic into the literal
positive-index inverse-index l2 space. All positive indices are retained. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS

def inverseBracketSquaredLatticeError (a c : ℂ) (d : Coeff 2) : Coeff 2 :=
  ⟨fun k => inverseBracketCoefficients k*((a*k+d k)^2-c-(a*k)^2),
    memlp_inverseBracket_squared_lattice_error a c d⟩

theorem analyticAt_inverseBracketSquaredLatticeError (a c : ℂ) (d : Coeff 2) :
    AnalyticAt ℂ (inverseBracketSquaredLatticeError a c) d := by
  let m : Coeff ⊤ := ⟨fun k => (k:ℂ)*inverseBracketCoefficients k,
    memℓp_infty ⟨1,by rintro _ ⟨k,rfl⟩; exact norm_index_mul_inverseBracket_le_one k⟩⟩
  let B : Coeff ⊤ := Coeff.exponentInclusion (p := 2) le_top inverseBracketCoefficients
  let square : Coeff 2 → Coeff 2 := fun v =>
    Coeff.multiplier (Coeff.exponentInclusion (p := 2) le_top v) v
  have hs : AnalyticAt ℂ square d :=
    ((Coeff.multiplierBilinear (p := 2)).analyticAt_bilinear _).comp₂
      ((Coeff.exponentInclusion (p := 2) le_top).analyticAt d) analyticAt_id
  have he : inverseBracketSquaredLatticeError a c = fun v =>
      (2*a) • Coeff.multiplierCLM m v+Coeff.multiplierCLM B (square v)-c • inverseBracketCoefficients := by
    funext v
    ext k
    change inverseBracketCoefficients k*((a*k+v k)^2-c-(a*k)^2) =
      (2*a)*(((k:ℂ)*inverseBracketCoefficients k)*v k)+
        inverseBracketCoefficients k*(v k*v k)-c*inverseBracketCoefficients k
    ring
  rw [he]
  exact (((Coeff.multiplierCLM m).analyticAt d).const_smul (c := 2*a)).add
    (((Coeff.multiplierCLM B).analyticAt (square d)).comp hs) |>.sub analyticAt_const

namespace LpSequence

def positiveRestriction (a : Coeff 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => a ((m:ℕ):ℤ), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    exact ((lp.memℓp a).summable (by norm_num)).comp_injective
      (fun i j h => Subtype.ext (Int.ofNat.inj h))⟩

theorem norm_positiveRestriction_le (a : Coeff 2) : ‖positiveRestriction a‖ ≤ ‖a‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal) (norm_nonneg a)
  intro S
  let e : ℕ+ ↪ ℤ := ⟨fun m => ((m:ℕ):ℤ),fun i j h => Subtype.ext (Int.ofNat.inj h)⟩
  simpa only [positiveRestriction,Finset.sum_map,e,Function.Embedding.coeFn_mk] using!
    lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) a (S.map e)

def positiveRestrictionCLM : Coeff 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := positiveRestriction
      map_add' := fun a b => by ext m; rfl
      map_smul' := fun c a => by ext m; rfl }
    1 (fun a => by change ‖positiveRestriction a‖ ≤ 1*‖a‖; simpa only [one_mul] using norm_positiveRestriction_le a)

theorem norm_positiveBracketRatio_le_two (m : ℕ+) : ‖(1+(m:ℕ):ℂ)/(m:ℕ)‖ ≤ 2 := by
  have hm : (1:ℝ) ≤ (m:ℕ) := by exact_mod_cast m.property
  have he : (1+(m:ℕ):ℂ) = ((1+(m:ℕ):ℝ):ℂ) := by simp
  rw [norm_div,he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity),Complex.norm_natCast]
  exact (div_le_iff₀ (by linarith : (0:ℝ) < (m:ℕ))).mpr (by linarith)

def positiveBracketToIndex (a : Coeff 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => ((1+(m:ℕ):ℂ)/(m:ℕ))*a ((m:ℕ):ℤ), by
    apply (((lp.memℓp (positiveRestriction a)).norm).const_mul (2:ℝ)).mono
    intro m
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_positiveBracketRatio_le_two m) (norm_nonneg _)⟩

theorem norm_positiveBracketToIndex_le (a : Coeff 2) : ‖positiveBracketToIndex a‖ ≤ 2*‖a‖ := by
  have h : ‖positiveBracketToIndex a‖ ≤ ‖(2:ℂ) • positiveRestriction a‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    change ‖((1+(m:ℕ):ℂ)/(m:ℕ))*a ((m:ℕ):ℤ)‖ ≤ ‖(2:ℂ)*a ((m:ℕ):ℤ)‖
    rw [norm_mul,norm_mul,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_right (norm_positiveBracketRatio_le_two m) (norm_nonneg _)
  rw [norm_smul,Complex.norm_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_positiveRestriction_le a) (by norm_num))

def positiveBracketToIndexCLM : Coeff 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := positiveBracketToIndex
      map_add' := fun a b => by ext m; exact mul_add _ _ _
      map_smul' := fun c a => by ext m; exact mul_left_comm _ _ _ }
    2 norm_positiveBracketToIndex_le

theorem positiveBracketToIndexCLM_apply (a : Coeff 2) (m : ℕ+) :
    positiveBracketToIndexCLM a m = ((1+(m:ℕ):ℂ)/(m:ℕ))*a ((m:ℕ):ℤ) := rfl

end LpSequence

def positiveSquaredLatticeError (a c : ℂ) (d : Coeff 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  LpSequence.positiveBracketToIndexCLM (inverseBracketSquaredLatticeError a c d)

theorem positiveSquaredLatticeError_apply (a c : ℂ) (d : Coeff 2) (m : ℕ+) :
    positiveSquaredLatticeError a c d m = ((a*(m:ℕ)+d (m:ℕ))^2-c-(a*(m:ℕ))^2)/(m:ℕ) := by
  change ((1+(m:ℕ):ℂ)/(m:ℕ))*(inverseBracketCoefficients (m:ℕ)*_) = _
  have hB : inverseBracketCoefficients (m:ℕ) = (1+(m:ℕ):ℂ)⁻¹ := by
    change (Weight.sobolev 1 (m:ℕ):ℂ)⁻¹ = _
    simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,Nat.abs_cast,Complex.ofReal_add,
      Complex.ofReal_one,Complex.ofReal_natCast]
  rw [hB]
  simp only [Int.cast_natCast]
  have hne : (1+(m:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : 1+(m:ℕ) ≠ 0)
  field_simp [hne]

theorem analyticAt_positiveSquaredLatticeError (a c : ℂ) (d : Coeff 2) :
    AnalyticAt ℂ (positiveSquaredLatticeError a c) d :=
  (LpSequence.positiveBracketToIndexCLM.analyticAt _).comp
    (analyticAt_inverseBracketSquaredLatticeError a c d)

end NLS
