import NLS.ZakharovShabat.SourceMidpointProductFullDiscSup
import NLS.ZakharovShabat.SourceSingleRootMidpointBounds
import NLS.ComplexAnalysis.SignedProductEstimates
import NLS.SequenceSpaces.FractionalReciprocalRows

/-! Fractional decay of the ACTUAL full midpoint product from a weighted
summable displacement majorant. Includes u=0 and u=1, with exact constants. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤q)]

omit [Fact (1≤q)] in
theorem norm_sourceMidpointProductRow_sobolev_l1_bound
    (hp : p≠⊤) (hp1 : 1<p) (ψ : CoeffPair p) (α : Coeff q)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (D : ℝ) (hD : 0≤D) (g : Coeff 1)
    (hα : ∀ m, Weight.sobolev u m*‖α m‖≤D*‖g m‖)
    (n : ℤ) (z : ℂ) (C : ℝ) (hC : 1≤C)
    (hsep : ∀ m : ℤ, m≠n → |((n-m : ℤ) : ℝ)|≤C*
      ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖) :
    Weight.sobolev u n*‖sourceMidpointProductRow hp hp1 ψ α n z‖≤
      (2*(C*D)*‖g‖)*Real.exp (2*(C*D)*‖g‖) := by
  let f : ℤ → ℂ := fun m => if m=n then 0 else α m/
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)
  have hC0 : 0≤C := by linarith
  have hf (m : ℤ) : ‖f m‖≤(C*D)*Weight.sobolev (-u) m*‖g m‖*
      ‖Coeff.puncturedLattice 2 (by norm_num) (n-m)‖ := by
    by_cases hm : m=n
    · simp only [f,if_pos hm,norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hD)
        ((Weight.sobolev (-u)).positive m).le) (norm_nonneg _)) (norm_nonneg _)
    have hαm := Coeff.sobolev_bound_of_weighted_majorant u D α g hα m
    have hn : n-m≠0 := sub_ne_zero.mpr (Ne.symm hm)
    rw [Coeff.puncturedLattice_apply,if_neg hn,norm_inv,Complex.norm_intCast]
    dsimp only [f]
    rw [if_neg hm]
    calc
      _≤C*(‖α m‖/|((m-n : ℤ) : ℝ)|) :=
        norm_midpoint_displacement_div_le C hC n m (Ne.symm hm) _ _ _ (hsep m hm)
      _≤C*((D*Weight.sobolev (-u) m*‖g m‖)/|((m-n : ℤ) : ℝ)|) := by gcongr
      _=_ := by rw [Int.cast_sub,Int.cast_sub,abs_sub_comm];ring
  obtain ⟨hfs,hb⟩ := Coeff.summable_norm_reciprocal_of_sobolev_l1 u hu0 hu1 g f n (C*D) (mul_nonneg hC0 hD) hf
  let S := ∑' m, ‖f m‖
  let K := 2*(C*D)*‖g‖
  have hS : 0≤S := tsum_nonneg (fun _ => norm_nonneg _)
  have hweight : 1≤Weight.sobolev u n := by simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono hu0 n
  have hSK : S≤K := (le_mul_of_one_le_left hS hweight).trans hb
  have hprod : ‖(∏' m, (1+f m))-1‖≤S*Real.exp K := by
    have h := NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_exp_sub_one_le f hfs
    exact h.1.trans (h.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hSK) hS))
  change Weight.sobolev u n*‖(∏' m, (1+f m))-1‖≤K*Real.exp K
  calc
    _≤Weight.sobolev u n*(S*Real.exp K) := mul_le_mul_of_nonneg_left hprod ((Weight.sobolev u).positive n).le
    _=(Weight.sobolev u n*S)*Real.exp K := by ring
    _≤K*Real.exp K := mul_le_mul_of_nonneg_right hb (Real.exp_pos K).le

end NLS.ZakharovShabat
