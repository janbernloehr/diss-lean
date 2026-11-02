import NLS.KdV.ClassicalContourCoverage
import NLS.ZakharovShabat.SymmetricEigenvalues
import NLS.ZakharovShabat.CompleteParitySpectrum

/-! # Actual high Hill energy pairs and their analytic symmetric data

The original counted frequency pairs are transferred through the
injective coordinate lambda=z^2 on each positive high disc. Both actual
Hill zeros retain their analytic multiplicities, also when they coincide.
The energy midpoint and squared gap are analytic symmetric functions of
the potential; no analytic ordering of individual roots is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The energy region bounded by the mapped high contour. -/
def classicalHillHighEnergyRegion (n : ℕ+) : Set ℂ :=
  (fun z : ℂ => z^2) '' ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)

def classicalHillHighMidpoint (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) : ℂ :=
  (periodicMidpoint (by simp) (classicalHillCoefficientPotential q) (n : ℤ))^2 +
    periodicSquaredGap (by simp) (classicalHillCoefficientPotential q) (n : ℤ)/4

def classicalHillHighSquaredGap (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) : ℂ :=
  4*(periodicMidpoint (by simp) (classicalHillCoefficientPotential q) (n : ℤ))^2 *
    periodicSquaredGap (by simp) (classicalHillCoefficientPotential q) (n : ℤ)

/-- The pair is specified by the actual Hill zeros, their multiplicities,
trace levels, and intrinsic analytic symmetric data. -/
structure ClassicalHillHighGapPair (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+)
    (l r : ℂ) : Prop where
  left_mem : l ∈ classicalHillHighEnergyRegion n
  right_mem : r ∈ classicalHillHighEnergyRegion n
  left_zero : classicalHillRadicand (l,q) = 0
  right_zero : classicalHillRadicand (r,q) = 0
  zeros_iff : ∀ lam ∈ classicalHillHighEnergyRegion n,
    classicalHillRadicand (lam,q) = 0 ↔ lam = l ∨ lam = r
  multiplicity : ∀ lam ∈ classicalHillHighEnergyRegion n,
    analyticOrderNatAt (fun w : ℂ => classicalHillRadicand (w,q)) lam = ({l,r} : Multiset ℂ).count lam
  trace_left : classicalHillDiscriminant q l = if (n : ℤ) % 2 = 0 then 2 else -2
  trace_right : classicalHillDiscriminant q r = if (n : ℤ) % 2 = 0 then 2 else -2
  midpoint_eq : classicalHillHighMidpoint q n = (l+r)/2
  squaredGap_eq : classicalHillHighSquaredGap q n = (l-r)^2

/-- The actual high spectral roots have the trace level fixed by the
index parity, including complex perturbations and repeated roots. -/
theorem classicalHillDiscriminant_high_root_level
    (q : NLS.LinearVolterra.Curve ℂ) (N : ℕ)
    (h : PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) (z : ℂ)
    (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4))
    (hzero : classicalHillRadicand (z^2,q) = 0) :
    classicalHillDiscriminant q (z^2) = if (n : ℤ) % 2 = 0 then 2 else -2 := by
  have hz' : z ∈ ball ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) := by simpa using hz
  have hn' : N < (n : ℤ).natAbs := by simpa using hn
  have hspec := (classicalHillRadicand_sq_eq_zero_iff_periodicSpectrum q z).mp hzero
  have hpos := (periodicAlgebraicMultiplicity_pos_iff (by simp) _ z).mpr hspec
  have hroot := h.disk_rootSpace_parity (classicalHillCoefficientPotential_even q) (n : ℤ) hn' z hz'
  have hsector (r : ℤ) (hr : (n : ℤ) % 2 = r % 2) :
      parityAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) r z =
        periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) z := by
    apply parityAlgebraicMultiplicity_eq_of_root_le
    rw [← pairParitySubspace_eq_of_emod_eq (n : ℤ) r hr]
    exact hroot
  rw [classicalHillDiscriminant_sq,← canonicalDiscriminant_classicalHillCoefficientPotential]
  by_cases he : (n : ℤ) % 2 = 0
  · rw [if_pos he]
    apply (canonicalDiscriminant_parity_levels _ (classicalHillCoefficientPotential_even q) z).1.mpr
    rw [hsector 0 (by simpa using he)]
    exact hpos
  · rw [if_neg he]
    apply (canonicalDiscriminant_parity_levels _ (classicalHillCoefficientPotential_even q) z).2.mpr
    rw [hsector 1 (by omega)]
    exact hpos

private theorem counted_pair_multiplicity
    (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) (x y : ℂ)
    (hset : enclosedPeriodicSpectrum (by simp) (classicalHillCoefficientPotential q)
      ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) = {x,y})
    (hm : if x = y then periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) x = 2 else
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) x = 1 ∧
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) y = 1) :
    ∀ z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) z =
        ({x,y} : Multiset ℂ).count z := by
  classical
  intro z hz
  have hnone (hx : z ≠ x) (hy : z ≠ y) :
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) z = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hspec := (periodicAlgebraicMultiplicity_pos_iff (by simp) _ z).mp hp
    have hmem := (mem_enclosedPeriodicSpectrum (by simp) (classicalHillCoefficientPotential q)
      ((Real.pi : ℂ)*(n : ℤ)) z (Real.pi/4)).mpr ⟨hspec,by simpa using hz⟩
    rw [hset] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    exact hmem.elim hx hy
  by_cases hxy : x = y
  · subst y
    have hm2 : periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) x = 2 := by
      simpa only [ite_true] using hm
    by_cases hz : z = x
    · subst z
      simp [hm2]
    · simp [hnone hz hz,hz]
  · have hm1 := by simpa only [if_neg hxy] using hm
    by_cases hzx : z = x
    · subst z
      simp [hm1.1,hxy]
    · by_cases hzy : z = y
      · subst z
        simp [hm1.2,hxy,Ne.symm hxy]
      · simp [hnone hzx hzy,hzx,hzy]

/-- The existing counted frequency pair yields two actual Hill energy
zeros with the exact energy multiplicities and normalization. -/
theorem exists_classicalHillHighGapPair_of_counting
    (q : NLS.LinearVolterra.Curve ℂ) (N : ℕ)
    (h : PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) : ∃ l r : ℂ, ClassicalHillHighGapPair q n l r := by
  classical
  have hn' : N < (n : ℤ).natAbs := by simpa using hn
  obtain ⟨x,y,hset,hm⟩ := h.disk_eigenvalue_pair (n : ℤ) hn'
  have hmem (z : ℂ) : z = x ∨ z = y →
      z ∈ periodicSpectrum (by simp) (classicalHillCoefficientPotential q) ∧
        z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    intro hz
    have hm : z ∈ enclosedPeriodicSpectrum (by simp) (classicalHillCoefficientPotential q)
        ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) := by rw [hset]; simpa using hz
    simpa using (mem_enclosedPeriodicSpectrum (by simp) _ _ z _).mp hm
  have hx := hmem x (Or.inl rfl)
  have hy := hmem y (Or.inr rfl)
  have hzero (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      classicalHillRadicand (z^2,q) = 0 ↔ z = x ∨ z = y := by
    rw [classicalHillRadicand_sq_eq_zero_iff_periodicSpectrum]
    have he := mem_enclosedPeriodicSpectrum (by simp) (classicalHillCoefficientPotential q)
      ((Real.pi : ℂ)*(n : ℤ)) z (Real.pi/4)
    rw [hset] at he
    simpa [hz] using he.symm
  have hcount := counted_pair_multiplicity q n x y hset hm
  have hinj := sq_injOn_high_closedBall n n.property
  have hxeq (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      z^2 = x^2 ↔ z = x := ⟨fun he => hinj (ball_subset_closedBall hz) (ball_subset_closedBall hx.2) he,
        fun he => congrArg (fun z : ℂ => z^2) he⟩
  have hyeq (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      z^2 = y^2 ↔ z = y := ⟨fun he => hinj (ball_subset_closedBall hz) (ball_subset_closedBall hy.2) he,
        fun he => congrArg (fun z : ℂ => z^2) he⟩
  have hsymmetric := h.midpoint_squaredGap_eq_pair (n : ℤ) hn' x y hset
  refine ⟨x^2,y^2,⟨⟨x,hx.2,rfl⟩,⟨y,hy.2,rfl⟩,
    (hzero x hx.2).mpr (Or.inl rfl),(hzero y hy.2).mpr (Or.inr rfl),?_,?_,
    classicalHillDiscriminant_high_root_level q N h n hn x hx.2 ((hzero x hx.2).mpr (Or.inl rfl)),
    classicalHillDiscriminant_high_root_level q N h n hn y hy.2 ((hzero y hy.2).mpr (Or.inr rfl)),?_,?_⟩⟩
  · rintro lam ⟨z,hz,rfl⟩
    rw [hzero z hz,hxeq z hz,hyeq z hz]
  · rintro lam ⟨z,hz,rfl⟩
    have hz0 : z ≠ 0 := by
      intro he
      have hp := re_pos_of_high_closedBall n n.property z (ball_subset_closedBall hz)
      simp only [he,zero_re,lt_self_iff_false] at hp
    rw [analyticOrderNatAt_classicalHillRadicand_energy q z hz0,hcount z hz]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,hxeq z hz,hyeq z hz]
  · dsimp only [classicalHillHighMidpoint]
    rw [hsymmetric.1,hsymmetric.2]
    ring
  · dsimp only [classicalHillHighSquaredGap]
    rw [hsymmetric.1,hsymmetric.2]
    ring

/-- The actual pair is unique up to exchange, also at a collapsed gap. -/
theorem ClassicalHillHighGapPair.eq_or_swap
    {q : NLS.LinearVolterra.Curve ℂ} {n : ℕ+} {l r a b : ℂ}
    (h : ClassicalHillHighGapPair q n l r) (k : ClassicalHillHighGapPair q n a b) :
    (l = a ∧ r = b) ∨ (l = b ∧ r = a) := by
  have hm := h.midpoint_eq.symm.trans k.midpoint_eq
  have hg := h.squaredGap_eq.symm.trans k.squaredGap_eq
  rcases eq_or_eq_neg_of_sq_eq_sq (l-r) (a-b) hg with hd | hd
  · left
    constructor
    · linear_combination hm+hd/2
    · linear_combination hm-hd/2
  · right
    constructor
    · linear_combination hm+hd/2
    · linear_combination hm-hd/2

/-- The energy midpoint and squared gap are analytic at every potential
whose high circle has the existing spectral counting data. -/
theorem analyticAt_classicalHillHigh_symmetric
    (q : NLS.LinearVolterra.Curve ℂ) (N : ℕ)
    (h : PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) :
    AnalyticAt ℂ (fun a => classicalHillHighMidpoint a n) q ∧
      AnalyticAt ℂ (fun a => classicalHillHighSquaredGap a n) q := by
  have hc := h.disk_resolvent (n : ℤ) (by simpa using hn)
  have ha := analyticAt_contourMidpoint_and_squaredGap (by simp) (classicalHillCoefficientPotential q)
    ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) (by positivity) hc
  have hB := analyticOnNhd_classicalHillCoefficientPotential q (mem_univ _)
  have hm : AnalyticAt ℂ (fun a => periodicMidpoint (by simp) (classicalHillCoefficientPotential a) (n : ℤ)) q :=
    ha.1.comp (f := classicalHillCoefficientPotential) hB
  have hg : AnalyticAt ℂ (fun a => periodicSquaredGap (by simp) (classicalHillCoefficientPotential a) (n : ℤ)) q :=
    ha.2.comp (f := classicalHillCoefficientPotential) hB
  exact ⟨(hm.pow 2).add hg.div_const,(analyticAt_const.mul (hm.pow 2)).mul hg⟩

end NLS.KdV
