import NLS.ZakharovShabat.SourcePsiGapFactorization
import NLS.ZakharovShabat.SourcePsiFreeCircleVariation
import NLS.ZakharovShabat.SourcePsiQuotientDiscMajorant

/-!
# The omitted-root denominator on free-centered psi contours

On the deleted-coordinate parameter space, the omitted root is fixed
at `πn`. A quarter-π disc about a different free center `πm` stays a
distance proportional to `|n-m|` from that root. Thus the `n-m`
coefficient in (2.27) is canceled uniformly by its denominator.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Free lattice separation on a quarter-π disc, with the exact
index factor retained. -/
theorem free_lattice_distance_lower_on_quarter_disc
    (n m : ℤ) (hnm : n ≠ m) (R : ℝ)
    (hR : R ≤ Real.pi/4) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R) :
    (Real.pi/2) * |((n-m : ℤ) : ℝ)| ≤
      ‖((Real.pi : ℂ)*n)-z‖ := by
  have hd : 1 ≤ |((n-m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
  have hcenter :
      dist ((Real.pi : ℂ)*n) ((Real.pi : ℂ)*m) =
        Real.pi * |((n-m : ℤ) : ℝ)| := by
    simpa only [dist_eq_norm] using norm_free_center_sub n m
  have htri := dist_triangle ((Real.pi : ℂ)*n) z ((Real.pi : ℂ)*m)
  rw [hcenter,dist_eq_norm] at htri
  have hzR : dist z ((Real.pi : ℂ)*m) ≤ R := mem_closedBall.mp hz
  nlinarith [Real.pi_pos]

/-- For a deleted root sequence, the omitted-root denominator controls
the index prefactor uniformly on every distant free quarter-π disc. -/
theorem norm_deletedPsi_omittedRoot_ratio_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (R : ℝ) (hR : R ≤ Real.pi/4) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R) :
    ‖(((n-m : ℤ) : ℂ) /
      (displacedRoots (a : Coeff p) n-z))‖ ≤ 2/Real.pi := by
  have ha : (a : Coeff p) n = 0 := a.property
  have hroot : displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [displacedRoots,ha]
  have hsep := free_lattice_distance_lower_on_quarter_disc
    n m hnm R hR z hz
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    have h := Int.one_le_abs (sub_ne_zero.mpr hnm)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  have hden : 0 < ‖(Real.pi : ℂ)*n-z‖ := by
    nlinarith [Real.pi_pos]
  rw [hroot, norm_div, Complex.norm_intCast]
  apply (div_le_iff₀ hden).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ Real.pi_pos).2
  nlinarith [hsep]

/-- A quotient-disc majorant controls the weighted regular factor in
the psi equation, uniformly in the deleted index. -/
theorem norm_deletedPsi_gapRegularFactor_weighted_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (B : Coeff p)
    (R : ℝ) (hR : R ≤ Real.pi/4) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R)
    (hquot : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖(((n-m : ℤ) : ℂ) *
      sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)‖ ≤
        (2/Real.pi) * (1+‖B m‖) := by
  let Q : ℂ := sourceSingleRootQuotientJointProduct hp hp1 m
    (z,((a : Coeff p),ψ))
  have hratio := norm_deletedPsi_omittedRoot_ratio_le
    n m hnm a R hR z hz
  have hQ : ‖Q‖ ≤ 1+‖B m‖ := by
    calc
      ‖Q‖ = ‖(Q-1)+1‖ := by ring_nf
      _ ≤ ‖Q-1‖+‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1+‖B m‖ := by
        dsimp [Q] at hquot ⊢
        norm_num at *
        linarith
  have heq : (((n-m : ℤ) : ℂ) *
      sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z) =
      ((((n-m : ℤ) : ℂ) /
        (displacedRoots (a : Coeff p) n-z)) * (I*Q)) := by
    dsimp [sourcePsiGapRegularFactor,Q]
    ring_nf
  rw [heq,norm_mul,norm_mul,Complex.norm_I,one_mul]
  calc
    ‖(((n-m : ℤ) : ℂ) /
      (displacedRoots (a : Coeff p) n-z))‖ * ‖Q‖ ≤
        (2/Real.pi)*‖Q‖ :=
      mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ ≤ (2/Real.pi)*(1+‖B m‖) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)

/-- Near the free source, the weighted regular factor of the actual
psi integrand has an `ℓᵖ` row majorant on all sufficiently distant
free quarter-π discs, uniformly in the omitted index. -/
theorem exists_local_deletedPsi_gapRegularFactor_tailMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V, ∀ n : ℤ,
        ∀ a : DeletedCoeff p n,
          ∃ B : Coeff p,
            ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
              ∀ z ∈ refinedResonantDisk m,
                ‖(((n-m : ℤ) : ℂ) *
                  sourcePsiGapRegularFactor hp hp1 n m
                    (a : Coeff p) ψ z)‖ ≤
                    (2/Real.pi)*(1+‖B m‖) := by
  obtain ⟨N,ε,hε,V,hVopen,hzero,K,hNK,hmajor⟩ :=
    exists_local_sourcePsiQuotient_lpDiscMajorant hp hp1
      (0 : CoeffPair p) (by simp)
  refine ⟨V,hVopen,hzero,K,?_⟩
  intro ψ hψ n a
  obtain ⟨B,hB⟩ := hmajor ψ hψ (a : Coeff p)
  refine ⟨B,?_⟩
  intro m hm hmn z hz
  have hN : ¬m.natAbs ≤ N := by omega
  have hzdisc : z ∈ sourceIsolatingDisc hp hp1
      (0 : CoeffPair p) N ε m := by
    simpa only [sourceIsolatingDisc,if_neg hN] using hz
  have hzclosed : z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/4) :=
    ball_subset_closedBall hz
  exact norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m (Ne.symm hmn) a ψ B
      (Real.pi/4) le_rfl z hzclosed (hB m hm z hzdisc)

end NLS.ZakharovShabat
