import NLS.KdV.HillL2DiscAsymptotics
import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealSpectrum
import NLS.KdV.ClassicalHighGapPairs
import NLS.ZakharovShabat.PeriodicCounting

/-! # Actual unordered high Hill pairs in the complex L2 topology

The checked canonical first-order realization transfers actual trace
zeros, multiplicities and parity levels through lambda=z^2. Symmetric
pair data are analytic in L2; no analytic ordering of individual roots
is assumed. One complex neighborhood supports the whole high family.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual radicand vanishes precisely at the existing periodic ZS
spectrum. This is a proved physical comparison, not assumed spectral data. -/
theorem hillL2Radicand_sq_eq_zero_iff_periodicSpectrum
    (q : Coeff 2) (z : ℂ) :
    hillL2Radicand q (z^2) = 0 ↔
      z ∈ periodicSpectrum (by simp) (hillL2CoefficientPotential q) := by
  change hillL2Discriminant q (z^2)^2-4 = 0 ↔ _
  rw [sub_eq_zero,← canonicalDiscriminant_hillL2CoefficientPotential]
  exact canonicalDiscriminant_sq_eq_four_iff _ (hillL2CoefficientPotential_even q) z

/-- The frequency pullback has exactly the original spectral algebraic
multiplicity, including double zeros. -/
theorem analyticOrderNatAt_hillL2Radicand_sq (q : Coeff 2) (z : ℂ) :
    analyticOrderNatAt (fun w : ℂ => hillL2Radicand q (w^2)) z =
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) z := by
  have he : (fun w : ℂ => hillL2Radicand q (w^2)) =
      canonicalPeriodicProduct (by simp) (hillL2CoefficientPotential q) := by
    funext w
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four _ (hillL2CoefficientPotential_even q),
      canonicalDiscriminant_hillL2CoefficientPotential]
    rfl
  rw [he]
  exact analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num) _ z

/-- Squaring the frequency coordinate preserves the analytic order at
every nonzero frequency. -/
theorem analyticOrderNatAt_hillL2Radicand_energy (q : Coeff 2)
    (z : ℂ) (hz : z ≠ 0) :
    analyticOrderNatAt (fun lam : ℂ => hillL2Radicand q (lam)) (z^2) =
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) z := by
  have hd : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hg : AnalyticAt ℂ (fun w : ℂ => w^2) z := analyticAt_id.pow 2
  have hdn : deriv (fun w : ℂ => w^2) z ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have he := analyticOrderAt_comp_of_deriv_ne_zero (f := fun lam : ℂ => hillL2Radicand q (lam))
    hg hdn
  have hn := congrArg ENat.toNat he
  change analyticOrderNatAt (fun w : ℂ => hillL2Radicand q (w^2)) z =
    analyticOrderNatAt (fun lam : ℂ => hillL2Radicand q (lam)) (z^2) at hn
  rw [← hn]
  exact analyticOrderNatAt_hillL2Radicand_sq q z

/-- One common cutoff and open neighborhood support the actual complex
periodic counting data near every potential in a compact set. -/
theorem exists_hillL2Counting_near_compact
    (K : Set (Coeff 2)) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ q ∈ V, ∀ M : ℕ, N ≤ M →
        PeriodicCountingData (by simp) (hillL2CoefficientPotential q) M := by
  classical
  have hl (q : K) : ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < N ∧ IsOpen V ∧ q.val ∈ V ∧ ∀ a ∈ V, ∀ M : ℕ, N ≤ M →
        PeriodicCountingData (by simp) (hillL2CoefficientPotential a) M := by
    obtain ⟨N,U,hN,hU,_,hq,_,_,_,hd⟩ :=
      exists_uniform_periodicCountingData (by simp) (hillL2CoefficientPotential q.val)
    exact ⟨N,hillL2CoefficientPotential ⁻¹' U,hN,
      hU.preimage continuous_hillL2CoefficientPotential,hq,fun a ha M hM => hd _ ha M hM⟩
  choose N V hN hV hqV hd using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨1+∑ q ∈ S, N q,⋃ q ∈ S, V q,by omega,
    isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,?_⟩
  intro q hq M hM
  obtain ⟨a,ha⟩ := mem_iUnion.mp hq
  obtain ⟨haS,hqa⟩ := mem_iUnion.mp ha
  have hNa : N a ≤ ∑ b ∈ S, N b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) haS
  exact hd a q hqa M (by omega)

/-- The energy region bounded by the mapped high contour. -/
def hillL2HighEnergyRegion (n : ℕ+) : Set ℂ :=
  (fun z : ℂ => z^2) '' ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)

def hillL2HighMidpoint (q : Coeff 2) (n : ℕ+) : ℂ :=
  (periodicMidpoint (by simp) (hillL2CoefficientPotential q) (n : ℤ))^2 +
    periodicSquaredGap (by simp) (hillL2CoefficientPotential q) (n : ℤ)/4

def hillL2HighSquaredGap (q : Coeff 2) (n : ℕ+) : ℂ :=
  4*(periodicMidpoint (by simp) (hillL2CoefficientPotential q) (n : ℤ))^2 *
    periodicSquaredGap (by simp) (hillL2CoefficientPotential q) (n : ℤ)

/-- The pair is specified by the actual Hill zeros, their multiplicities,
trace levels, and intrinsic analytic symmetric data. -/
structure HillL2HighGapPair (q : Coeff 2) (n : ℕ+)
    (l r : ℂ) : Prop where
  left_mem : l ∈ hillL2HighEnergyRegion n
  right_mem : r ∈ hillL2HighEnergyRegion n
  left_zero : hillL2Radicand q (l) = 0
  right_zero : hillL2Radicand q (r) = 0
  zeros_iff : ∀ lam ∈ hillL2HighEnergyRegion n,
    hillL2Radicand q (lam) = 0 ↔ lam = l ∨ lam = r
  multiplicity : ∀ lam ∈ hillL2HighEnergyRegion n,
    analyticOrderNatAt (fun w : ℂ => hillL2Radicand q (w)) lam = ({l,r} : Multiset ℂ).count lam
  trace_left : hillL2Discriminant q l = if (n : ℤ) % 2 = 0 then 2 else -2
  trace_right : hillL2Discriminant q r = if (n : ℤ) % 2 = 0 then 2 else -2
  midpoint_eq : hillL2HighMidpoint q n = (l+r)/2
  squaredGap_eq : hillL2HighSquaredGap q n = (l-r)^2

theorem HillL2HighGapPair.swap
    {q : Coeff 2} {n : ℕ+} {l r : ℂ}
    (h : HillL2HighGapPair q n l r) : HillL2HighGapPair q n r l := by
  refine ⟨h.right_mem,h.left_mem,h.right_zero,h.left_zero,?_,?_,h.trace_right,h.trace_left,?_,?_⟩
  · intro lam hlam
    rw [h.zeros_iff lam hlam,or_comm]
  · intro lam hlam
    rw [h.multiplicity lam hlam,Multiset.pair_comm]
  · rw [h.midpoint_eq,add_comm l r]
  · rw [h.squaredGap_eq]
    ring

/-- The actual L2 operator reality theorem applies to both endpoints,
including a double root; no continuous representative is needed. -/
theorem HillL2HighGapPair.im_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    {n : ℕ+} {l u : ℂ} (p : HillL2HighGapPair (SpectralWeight.one.toCoeff q) n l u) :
    l.im = 0 ∧ u.im = 0 := by
  exact ⟨hillL2Discriminant_root_im_zero q hq hreal l (sub_eq_zero.mp p.left_zero),
    hillL2Discriminant_root_im_zero q hq hreal u (sub_eq_zero.mp p.right_zero)⟩

/-- The actual high spectral roots have the trace level fixed by the
index parity, including complex perturbations and repeated roots. -/
theorem hillL2Discriminant_high_root_level
    (q : Coeff 2) (N : ℕ)
    (h : PeriodicCountingData (by simp) (hillL2CoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) (z : ℂ)
    (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4))
    (hzero : hillL2Radicand q (z^2) = 0) :
    hillL2Discriminant q (z^2) = if (n : ℤ) % 2 = 0 then 2 else -2 := by
  have hz' : z ∈ ball ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) := by simpa using hz
  have hn' : N < (n : ℤ).natAbs := by simpa using hn
  have hspec := (hillL2Radicand_sq_eq_zero_iff_periodicSpectrum q z).mp hzero
  have hpos := (periodicAlgebraicMultiplicity_pos_iff (by simp) _ z).mpr hspec
  have hroot := h.disk_rootSpace_parity (hillL2CoefficientPotential_even q) (n : ℤ) hn' z hz'
  have hsector (r : ℤ) (hr : (n : ℤ) % 2 = r % 2) :
      parityAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) r z =
        periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) z := by
    apply parityAlgebraicMultiplicity_eq_of_root_le
    rw [← pairParitySubspace_eq_of_emod_eq (n : ℤ) r hr]
    exact hroot
  rw [← canonicalDiscriminant_hillL2CoefficientPotential]
  by_cases he : (n : ℤ) % 2 = 0
  · rw [if_pos he]
    apply (canonicalDiscriminant_parity_levels _ (hillL2CoefficientPotential_even q) z).1.mpr
    rw [hsector 0 (by simpa using he)]
    exact hpos
  · rw [if_neg he]
    apply (canonicalDiscriminant_parity_levels _ (hillL2CoefficientPotential_even q) z).2.mpr
    rw [hsector 1 (by omega)]
    exact hpos

private theorem counted_pair_multiplicity
    (q : Coeff 2) (n : ℕ+) (x y : ℂ)
    (hset : enclosedPeriodicSpectrum (by simp) (hillL2CoefficientPotential q)
      ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) = {x,y})
    (hm : if x = y then periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) x = 2 else
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) x = 1 ∧
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) y = 1) :
    ∀ z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) z =
        ({x,y} : Multiset ℂ).count z := by
  classical
  intro z hz
  have hnone (hx : z ≠ x) (hy : z ≠ y) :
      periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) z = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hspec := (periodicAlgebraicMultiplicity_pos_iff (by simp) _ z).mp hp
    have hmem := (mem_enclosedPeriodicSpectrum (by simp) (hillL2CoefficientPotential q)
      ((Real.pi : ℂ)*(n : ℤ)) z (Real.pi/4)).mpr ⟨hspec,by simpa using hz⟩
    rw [hset] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    exact hmem.elim hx hy
  by_cases hxy : x = y
  · subst y
    have hm2 : periodicAlgebraicMultiplicity (by simp) (hillL2CoefficientPotential q) x = 2 := by
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
theorem exists_hillL2HighGapPair_of_counting
    (q : Coeff 2) (N : ℕ)
    (h : PeriodicCountingData (by simp) (hillL2CoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) : ∃ l r : ℂ, HillL2HighGapPair q n l r := by
  classical
  have hn' : N < (n : ℤ).natAbs := by simpa using hn
  obtain ⟨x,y,hset,hm⟩ := h.disk_eigenvalue_pair (n : ℤ) hn'
  have hmem (z : ℂ) : z = x ∨ z = y →
      z ∈ periodicSpectrum (by simp) (hillL2CoefficientPotential q) ∧
        z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    intro hz
    have hm : z ∈ enclosedPeriodicSpectrum (by simp) (hillL2CoefficientPotential q)
        ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) := by rw [hset]; simpa using hz
    simpa using (mem_enclosedPeriodicSpectrum (by simp) _ _ z _).mp hm
  have hx := hmem x (Or.inl rfl)
  have hy := hmem y (Or.inr rfl)
  have hzero (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      hillL2Radicand q (z^2) = 0 ↔ z = x ∨ z = y := by
    rw [hillL2Radicand_sq_eq_zero_iff_periodicSpectrum]
    have he := mem_enclosedPeriodicSpectrum (by simp) (hillL2CoefficientPotential q)
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
    hillL2Discriminant_high_root_level q N h n hn x hx.2 ((hzero x hx.2).mpr (Or.inl rfl)),
    hillL2Discriminant_high_root_level q N h n hn y hy.2 ((hzero y hy.2).mpr (Or.inr rfl)),?_,?_⟩⟩
  · rintro lam ⟨z,hz,rfl⟩
    rw [hzero z hz,hxeq z hz,hyeq z hz]
  · rintro lam ⟨z,hz,rfl⟩
    have hz0 : z ≠ 0 := by
      intro he
      have hp := re_pos_of_high_closedBall n n.property z (ball_subset_closedBall hz)
      simp only [he,zero_re,lt_self_iff_false] at hp
    rw [analyticOrderNatAt_hillL2Radicand_energy q z hz0,hcount z hz]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,hxeq z hz,hyeq z hz]
  · dsimp only [hillL2HighMidpoint]
    rw [hsymmetric.1,hsymmetric.2]
    ring
  · dsimp only [hillL2HighSquaredGap]
    rw [hsymmetric.1,hsymmetric.2]
    ring

/-- The actual pair is unique up to exchange, also at a collapsed gap. -/
theorem HillL2HighGapPair.eq_or_swap
    {q : Coeff 2} {n : ℕ+} {l r a b : ℂ}
    (h : HillL2HighGapPair q n l r) (k : HillL2HighGapPair q n a b) :
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
theorem analyticAt_hillL2High_symmetric
    (q : Coeff 2) (N : ℕ)
    (h : PeriodicCountingData (by simp) (hillL2CoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) :
    AnalyticAt ℂ (fun a => hillL2HighMidpoint a n) q ∧
      AnalyticAt ℂ (fun a => hillL2HighSquaredGap a n) q := by
  have hc := h.disk_resolvent (n : ℤ) (by simpa using hn)
  have ha := analyticAt_contourMidpoint_and_squaredGap (by simp) (hillL2CoefficientPotential q)
    ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) (by positivity) hc
  have hB := analyticOnNhd_hillL2CoefficientPotential q (mem_univ _)
  have hm : AnalyticAt ℂ (fun a => periodicMidpoint (by simp) (hillL2CoefficientPotential a) (n : ℤ)) q :=
    ha.1.comp (f := hillL2CoefficientPotential) hB
  have hg : AnalyticAt ℂ (fun a => periodicSquaredGap (by simp) (hillL2CoefficientPotential a) (n : ℤ)) q :=
    ha.2.comp (f := hillL2CoefficientPotential) hB
  exact ⟨(hm.pow 2).add hg.div_const,(analyticAt_const.mul (hm.pow 2)).mul hg⟩

end NLS.KdV
