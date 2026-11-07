import NLS.ZakharovShabat.SourceMidpointProductFractionalDecay
import NLS.ZakharovShabat.SourceSquaredGapFractionalDecay
import NLS.ZakharovShabat.SourceSingleRootGapCorrectionLimit

/-! Fractional decay of the ACTUAL infinite single-root quotient.
The midpoint product and squared-gap correction use the same branch. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceHilbertReciprocalNorm : ℝ :=
  ‖Coeff.puncturedLattice (2 : ℝ≥0∞).conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (2 : ℝ≥0∞) (2 : ℝ≥0∞).conjExponent).mp (by norm_num))‖

def sourceFractionalQuotientBound (C D L R : ℝ) : ℝ :=
  (2*(C*D)*R)*Real.exp (2*(C*D)*R)+
    Real.exp (C*L*sourceHilbertReciprocalNorm)*C^2*(2*R)

theorem sourceFractionalQuotientBound_nonnegative
    (C D L R : ℝ) (hC : 0≤C) (hD : 0≤D) (hR : 0≤R) :
    0≤sourceFractionalQuotientBound C D L R := by
  unfold sourceFractionalQuotientBound
  positivity

theorem norm_sourceSingleRootQuotient_sobolev_l1_bound
    (φ ψ : CoeffPair 2) (a α : Coeff 2)
    (hα : ∀ m : ℤ, displacedRoots a m-
      canonicalPeriodicMidpoint (by norm_num) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m=α m)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1)
    (D L R : ℝ) (hD : 0≤D) (hR : 0≤R) (hαnorm : ‖α‖≤L) (g : Coeff 1) (hgnorm : ‖g‖≤R)
    (hweighted : ∀ m, Weight.sobolev u m*‖α m‖≤D*‖g m‖)
    (hgap : ∀ m, Weight.sobolev u m*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ m‖^2≤‖g m‖)
    (N : ℕ) (ε C : ℝ) (hC : 1≤C)
    (hsep : ∀ i j : ℤ, i≠j → ∀ z∈sourceIsolatingDisc (by norm_num) (by norm_num) φ N ε i,
      |((i-j : ℤ) : ℝ)|≤C*‖canonicalPeriodicMidpoint (by norm_num) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (z : ℂ) (hz : z∈sourceIsolatingDisc (by norm_num) (by norm_num) φ N ε n)
    (hdom : (z,(a,ψ))∈sourceSingleRootQuotientJointDomain (by norm_num) (by norm_num) univ n)
    (hsmall : (C^2/4)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm (by norm_num) (by norm_num) ψ n m)≤1/2) :
    Weight.sobolev u n*‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) n (z,(a,ψ))-1‖≤
      sourceFractionalQuotientBound C D L R := by
  have hC0 : 0≤C := by linarith
  let P := sourceMidpointProductRow (by norm_num) (by norm_num) ψ α n z
  let Q := sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) n (z,(a,ψ))
  let κ := sourceHilbertReciprocalNorm
  have hκ : 0≤κ := by dsimp only [κ,sourceHilbertReciprocalNorm];exact lp.norm_nonneg' _
  let T := ∑' m : ℤ, sourceSquaredGapReciprocalTerm (by norm_num) (by norm_num) ψ n m
  have hP : Weight.sobolev u n*‖P‖≤(2*(C*D)*R)*Real.exp (2*(C*D)*R) := by
    have h := norm_sourceMidpointProductRow_sobolev_l1_bound (by norm_num) (by norm_num) ψ α
      u hu0 hu1 D hD g hweighted n z C hC (fun m hm => hsep n m (Ne.symm hm) z hz)
    exact h.trans (by gcongr)
  have hT0 : 0≤T := tsum_nonneg (fun m => by unfold sourceSquaredGapReciprocalTerm;split_ifs <;> positivity)
  have hT : Weight.sobolev u n*T≤2*R := by
    have h := sourceSquaredGapReciprocalRow_sobolev_l1_bound (by norm_num) (by norm_num) ψ
      u hu0 hu1 1 (by norm_num) g (fun m => by simpa only [one_mul] using hgap m) n
    exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hgnorm (by norm_num : (0 : ℝ)≤2))
  have hcor : ‖Q-(P+1)‖≤Real.exp (C*‖α‖*κ)*C^2*T :=
    norm_sourceSingleRootQuotientJointProduct_sub_midpoint_le_of_small_row
      (by norm_num) (by norm_num) (by norm_num) φ ψ a α hα N ε C hC hsep n z hz hdom hsmall
  have hexp : Real.exp (C*‖α‖*κ)≤Real.exp (C*L*κ) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαnorm hC0) hκ
  have hcor' : Weight.sobolev u n*‖Q-(P+1)‖≤Real.exp (C*L*κ)*C^2*(2*R) := by
    calc
      _≤Weight.sobolev u n*(Real.exp (C*‖α‖*κ)*C^2*T) :=
        mul_le_mul_of_nonneg_left hcor ((Weight.sobolev u).positive n).le
      _=(Real.exp (C*‖α‖*κ)*C^2)*(Weight.sobolev u n*T) := by ring
      _≤(Real.exp (C*L*κ)*C^2)*(2*R) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)) hT
          (mul_nonneg ((Weight.sobolev u).positive n).le hT0) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have he : Q-1=P+(Q-(P+1)) := by ring
  change Weight.sobolev u n*‖Q-1‖≤_
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) ((Weight.sobolev u).positive n).le).trans
    ((by rw [mul_add];exact add_le_add hP hcor') : _)

end NLS.ZakharovShabat
