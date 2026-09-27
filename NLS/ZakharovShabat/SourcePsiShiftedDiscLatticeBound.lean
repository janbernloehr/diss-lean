import NLS.ZakharovShabat.SourcePsiGlobalHeadDiscBound
import NLS.ZakharovShabat.SourcePsiFreeLatticeBound

/-!
# Lattice separation on shifted selected psi contours

For a finite nonstandard contour, sufficiently distant deleted indices
still have a denominator proportional to their lattice separation.
This lets the quotient-error majorant control the weighted regular
factor on the head contours as well as on free-centered tail contours.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A selected disc shifted from its free lattice center remains a
distance at least half the lattice separation from a sufficiently
distant deleted free root. -/
theorem shifted_disc_free_lattice_distance_lower
    (n m : ℤ) (c : ℂ) (R : ℝ)
    (hsep : 2*(‖c-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (z : ℂ) (hz : z ∈ closedBall c R) :
    (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤
      ‖((Real.pi : ℂ)*n)-z‖ := by
  let d : ℝ := |((n-m : ℤ) : ℝ)|
  have hcenter :
      ‖((Real.pi : ℂ)*n)-((Real.pi : ℂ)*m)‖ = Real.pi*d := by
    simpa only [dist_eq_norm] using norm_free_center_sub n m
  have hzR : ‖z-c‖ ≤ R := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have htri :
      ‖((Real.pi : ℂ)*n)-((Real.pi : ℂ)*m)‖ ≤
        ‖((Real.pi : ℂ)*n)-z‖+‖z-c‖+
          ‖c-(Real.pi : ℂ)*m‖ := by
    have heq : ((Real.pi : ℂ)*n)-((Real.pi : ℂ)*m) =
        (((Real.pi : ℂ)*n)-z)+(z-c)+(c-(Real.pi : ℂ)*m) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  dsimp [d] at hcenter ⊢
  nlinarith

/-- The omitted-root denominator cancels the equation's index weight
on a shifted selected disc once the deleted index is sufficiently far
from the selected index. -/
theorem norm_deletedPsi_omittedRoot_ratio_le_on_shifted_disc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (c : ℂ) (R : ℝ)
    (hsep : 2*(‖c-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (z : ℂ) (hz : z ∈ closedBall c R) :
    ‖(((n-m : ℤ) : ℂ) /
      (displacedRoots (a : Coeff p) n-z))‖ ≤ 2/Real.pi := by
  have ha : (a : Coeff p) n = 0 := a.property
  have hroot : displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n := by simp [displacedRoots,ha]
  have hdist := shifted_disc_free_lattice_distance_lower
    n m c R hsep z hz
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    have h := Int.one_le_abs (sub_ne_zero.mpr hnm)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  have hden : 0 < ‖(Real.pi : ℂ)*n-z‖ := by
    nlinarith [Real.pi_pos]
  rw [hroot,norm_div,Complex.norm_intCast]
  apply (div_le_iff₀ hden).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ Real.pi_pos).2
  nlinarith [hdist]

/-- A quotient-error majorant controls the weighted regular factor
on a shifted selected disc for every sufficiently distant deleted
index. -/
theorem norm_deletedPsi_gapRegularFactor_weighted_le_on_shifted_disc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (B : Coeff p)
    (c : ℂ) (R : ℝ)
    (hsep : 2*(‖c-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (z : ℂ) (hz : z ∈ closedBall c R)
    (hquot : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖(((n-m : ℤ) : ℂ) *
      sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)‖ ≤
        (2/Real.pi)*(1+‖B m‖) := by
  let Q : ℂ := sourceSingleRootQuotientJointProduct hp hp1 m
    (z,((a : Coeff p),ψ))
  have hratio := norm_deletedPsi_omittedRoot_ratio_le_on_shifted_disc
    n m hnm a c R hsep z hz
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

/-- For finitely many shifted selected discs, one lattice-distance
cutoff ensures the uniform omitted-root ratio bound for every disc
and every sufficiently distant deleted index. -/
theorem exists_uniform_shifted_disc_lattice_cutoff
    (s : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m ∈ s, 0 ≤ R m) :
    ∃ K : ℕ, ∀ m ∈ s, ∀ n : ℤ,
      K ≤ (n-m).natAbs →
        2*(‖c m-(Real.pi : ℂ)*m‖+R m) ≤
          Real.pi*|((n-m : ℤ) : ℝ)| := by
  let f : ℤ → ℝ := fun m => ‖c m-(Real.pi : ℂ)*m‖+R m
  let D : ℝ := ∑ m ∈ s, f m
  have hf (m : ℤ) (hm : m ∈ s) : 0 ≤ f m := by
    dsimp [f]
    exact add_nonneg (norm_nonneg _) (hR m hm)
  obtain ⟨K,hK⟩ := exists_nat_gt (2*D/Real.pi)
  have hKπ : 2*D ≤ Real.pi*(K:ℝ) := by
    have h : 2*D/Real.pi < (K:ℝ) := by exact_mod_cast hK
    have h' := (div_lt_iff₀ Real.pi_pos).mp h
    nlinarith
  refine ⟨K,?_⟩
  intro m hm n hn
  have hmD : f m ≤ D :=
    Finset.single_le_sum (f := f) (fun k hk => hf k hk) hm
  have habs : (K:ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
    have hcast : (K:ℝ) ≤ ((n-m).natAbs:ℝ) := by
      exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hcast
  have hπmul := mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  dsimp [f] at hmD
  nlinarith

end NLS.ZakharovShabat
