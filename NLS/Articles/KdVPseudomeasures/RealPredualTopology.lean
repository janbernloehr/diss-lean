import NLS.Articles.KdVPseudomeasures.SourceSpaces

/-! # Real Wiener testing on the physical source locus

The induced topology of evaluations against all real mean-zero even Wiener
coefficients agrees with the complex Wiener weak-star topology on every
norm-bounded subset of the source locus. The finite cosine/sine tests below
belong to the full real Wiener predual; neither a finite-p source topology
nor a norm topology is substituted for the endpoint weak-star topology.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- The paper's real, mean-zero, physically one-periodic Wiener predual,
in its exact weighted coefficient realization. -/
def RealWienerTest (r : ℝ) :=
  {b : WeightedCoeff (Weight.sobolev r) 1 //
    b.val 0 = 0 ∧ (∀ n : ℤ, b.val (-n) = star (b.val n)) ∧
      ∀ k : ℤ, b.val (2*k+1) = 0}

/-- Every test is an original real mean-zero period-one Wiener distribution. -/
theorem realWienerTest_original (r : ℝ) (b : RealWienerTest r) :
    ((sobolevCoefficients (L := 2) r 1).symm b.val).val.IsRealMeanZeroPeriodOne := by
  rw [Distribution.isRealMeanZeroPeriodOne_iff_coefficients]
  have hc (n : ℤ) : ((sobolevCoefficients (L := 2) r 1).symm b.val).val (mode (-n)) = b.val.val n :=
    congrArg (fun a : WeightedCoeff (Weight.sobolev r) 1 => a.val n)
      ((sobolevCoefficients (L := 2) r 1).apply_symm_apply b.val)
  constructor
  · simpa only [neg_zero] using (hc 0).trans b.property.1
  · constructor
    · intro n
      simpa only [neg_neg] using (hc (-n)).trans ((b.property.2.1 n).trans (congrArg star (hc n).symm))
    · intro k
      exact (hc (2*k+1)).trans (b.property.2.2 k)

/-- The real bilinear action on every original real Wiener test. -/
def realWienerEvaluations (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) : RealWienerTest r → ℝ :=
  fun b => (f b.val).re

theorem continuous_realWienerEvaluations (r : ℝ) : Continuous (realWienerEvaluations r) := by
  apply continuous_pi
  intro b
  exact Complex.continuous_re.comp (WeakDual.eval_continuous b.val)

/-- A finite conjugate pair, used as a cosine or sine test. -/
def wienerPair (r : ℝ) (n : ℤ) (c : ℂ) : WeightedCoeff (Weight.sobolev r) 1 :=
  WeightedCoeff.ofFinsupp _ _ (Finsupp.single n c + Finsupp.single (-n) (star c))

/-- Nonzero even modes yield tests within the paper's real Wiener predual. -/
def realWienerPair (r : ℝ) (n : ℤ) (hn0 : n ≠ 0) (hne : n % 2 = 0) (c : ℂ) :
    RealWienerTest r :=
  ⟨wienerPair r n c, by
    constructor
    · simp [wienerPair, WeightedCoeff.ofFinsupp_apply, hn0]
    · constructor
      · intro k
        have hs (P : Prop) [Decidable P] (z : ℂ) :
            star (if P then z else 0) = if P then star z else 0 := by
          split_ifs <;> simp
        simp only [wienerPair, WeightedCoeff.ofFinsupp_apply, Finsupp.add_apply,
          Finsupp.single_apply, star_add, hs, star_star, neg_inj]
        have hh : n = -k ↔ -n = k := by omega
        simp only [hh]
        exact add_comm _ _
      · intro k
        have h1 : n ≠ 2*k+1 := by omega
        have h2 : -n ≠ 2*k+1 := by omega
        simp [wienerPair, WeightedCoeff.ofFinsupp_apply, h1, h2]⟩

/-- A scalar unit-mode test recovers the opposite coefficient. -/
theorem eval_wienerSingle (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) (c : ℂ) :
    f (WeightedCoeff.ofFinsupp (Weight.sobolev r) 1 (Finsupp.single n c)) =
      c * WeightedCoeff.weakStarCoordinates r f (-n) := by
  have he : WeightedCoeff.ofFinsupp (Weight.sobolev r) 1 (Finsupp.single n c) =
      c • WeightedCoeff.ofFinsupp (Weight.sobolev r) 1 (Finsupp.single n 1) := by
    apply Subtype.ext
    funext k
    simp [WeightedCoeff.ofFinsupp_apply, Finsupp.single_apply]
  rw [he, map_smul]
  simp only [smul_eq_mul, WeightedCoeff.weakStarCoordinates, neg_neg]

/-- The complete finite pair action, before restricting to the real source locus. -/
theorem eval_wienerPair (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) (c : ℂ) :
    f (wienerPair r n c) = c * WeightedCoeff.weakStarCoordinates r f (-n) +
      star c * WeightedCoeff.weakStarCoordinates r f n := by
  have he : wienerPair r n c =
      WeightedCoeff.ofFinsupp _ 1 (Finsupp.single n c) +
        WeightedCoeff.ofFinsupp _ 1 (Finsupp.single (-n) (star c)) := by
    apply Subtype.ext
    rfl
  rw [he, map_add, eval_wienerSingle, eval_wienerSingle, neg_neg]

/-- Cosine/sine tests separate all potentials, including the zero and odd modes. -/
theorem realWienerEvaluations_injective_on_locus (r : ℝ) :
    Set.InjOn (realWienerEvaluations r) (potentialCoordinateLocus r) := by
  intro f hf g hg he
  apply WeightedCoeff.weakStarCoordinates_injective r
  funext n
  by_cases hn0 : n = 0
  · subst n
    exact hf.1.1.trans hg.1.1.symm
  by_cases hne : n % 2 = 0
  · have h1 := congrFun he (realWienerPair r n hn0 hne 1)
    have hI := congrFun he (realWienerPair r n hn0 hne Complex.I)
    change (f (wienerPair r n 1)).re = (g (wienerPair r n 1)).re at h1
    change (f (wienerPair r n Complex.I)).re = (g (wienerPair r n Complex.I)).re at hI
    rw [eval_wienerPair, eval_wienerPair, hf.1.2 n, hg.1.2 n] at h1 hI
    apply Complex.ext
    · simpa using (show (WeightedCoeff.weakStarCoordinates r f n).re =
        (WeightedCoeff.weakStarCoordinates r g n).re by
          simp only [one_mul, star_one, Complex.add_re, Complex.star_def,
            Complex.conj_re] at h1
          linarith)
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im] at hI
      linarith
  · have hn : n = 2*(n/2)+1 := by omega
    rw [hn, hf.2 (n/2), hg.2 (n/2)]

/-- On every bounded source subset, testing against the real Wiener predual
induces exactly the previously constructed endpoint weak-star topology. -/
theorem isEmbedding_realWienerEvaluations_on_bounded (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) (hA : A ⊆ potentialCoordinateLocus r) :
    Topology.IsEmbedding (fun f : A => realWienerEvaluations r f.val) := by
  let K := closure A
  have hK : IsCompact K := WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure hb) isClosed_closure
  have hKL : K ⊆ potentialCoordinateLocus r :=
    closure_minimal hA (isClosed_potentialCoordinateLocus r)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heK : Topology.IsClosedEmbedding (fun f : K => realWienerEvaluations r f.val) :=
    ((continuous_realWienerEvaluations r).comp continuous_subtype_val).isClosedEmbedding
      (fun f g he => Subtype.ext (realWienerEvaluations_injective_on_locus r
        (hKL f.property) (hKL g.property) he))
  let j : A → K := fun f => ⟨f.val, subset_closure f.property⟩
  have hej : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp Topology.IsEmbedding.subtypeVal
  exact heK.isEmbedding.comp hej

/-- All original real Wiener distributions, with the physical source constraints. -/
def OriginalRealWienerTest (r : ℝ) :=
  {u : FourierLebesgueSpace (2:ℝ) r 1 // u.val.IsRealMeanZeroPeriodOne}

/-- The real predual is the whole original real Wiener space, not just the
finite cosine/sine tests used to separate points in the proof. -/
def realWienerTestOriginalEquiv (r : ℝ) : RealWienerTest r ≃ OriginalRealWienerTest r where
  toFun b := ⟨(sobolevCoefficients r 1).symm b.val, realWienerTest_original r b⟩
  invFun u := ⟨sobolevCoefficients r 1 u.val, by
    have hu := Distribution.isRealMeanZeroPeriodOne_iff_coefficients u.val.val |>.mp u.property
    change u.val.val (mode (-0)) = 0 ∧
      (∀ n : ℤ, u.val.val (mode (-(-n))) = star (u.val.val (mode (-n)))) ∧
      ∀ k : ℤ, u.val.val (mode (-(2*k+1))) = 0
    simpa only [neg_zero, neg_neg] using hu⟩
  left_inv b := by apply Subtype.ext; exact LinearIsometryEquiv.apply_symm_apply _ _
  right_inv u := by apply Subtype.ext; exact LinearIsometryEquiv.symm_apply_apply _ _

/-- The full real predual correspondence preserves the original Wiener norm. -/
theorem norm_realWienerTestOriginalEquiv (r : ℝ) (b : RealWienerTest r) :
    ‖(realWienerTestOriginalEquiv r b).val‖ = ‖b.val‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- Testing the actual original-distribution weak dual against its actual
original real Wiener predual. -/
def originalRealWienerEvaluations (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) : OriginalRealWienerTest r → ℝ :=
  fun u => ((coefficientWeakDualHomeomorph (L := 2) r f) u.val).re

theorem realWienerEvaluations_eq_original (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (b : RealWienerTest r) :
    realWienerEvaluations r f b = originalRealWienerEvaluations r f (realWienerTestOriginalEquiv r b) := by
  change (f b.val).re = (f (sobolevCoefficients r 1 ((sobolevCoefficients (L := 2) r 1).symm b.val))).re
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- On every bounded physical source subset, the topology is exactly that
induced by evaluations against all original real Wiener tests. -/
theorem isEmbedding_originalRealWienerEvaluations_on_bounded (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) (hA : A ⊆ potentialCoordinateLocus r) :
    Topology.IsEmbedding (fun f : A => originalRealWienerEvaluations r f.val) := by
  have hc : Continuous (fun f : A => originalRealWienerEvaluations r f.val) := by
    apply continuous_pi
    intro u
    exact Complex.continuous_re.comp
      ((WeakDual.eval_continuous u.val).comp
        ((coefficientWeakDualHomeomorph (L := 2) r).continuous.comp continuous_subtype_val))
  have hg : Continuous (fun v : OriginalRealWienerTest r → ℝ =>
      fun b : RealWienerTest r => v (realWienerTestOriginalEquiv r b)) := by
    apply continuous_pi
    intro b
    exact continuous_apply _
  apply Topology.IsEmbedding.of_comp hc hg
  have he : ((fun v : OriginalRealWienerTest r → ℝ =>
      fun b : RealWienerTest r => v (realWienerTestOriginalEquiv r b)) ∘
      (fun f : A => originalRealWienerEvaluations r f.val)) =
      (fun f : A => realWienerEvaluations r f.val) := by
    funext f b
    exact (realWienerEvaluations_eq_original r f.val b).symm
  rw [he]
  exact isEmbedding_realWienerEvaluations_on_bounded r A hb hA

/-- For real source data and real Wiener tests the full complex action is
real, so taking its real part above loses no part of the physical pairing. -/
theorem realWienerAction_im_zero (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hf : f ∈ potentialCoordinateLocus r) (b : RealWienerTest r) :
    (f b.val).im = 0 := by
  have hr : f b.val = ∑' n : ℤ, b.val.val n * WeightedCoeff.weakStarCoordinates r f (-n) := by
    have hh := WeightedCoeff.sobolevBilinearPairing_sobolevCotangent (q := ⊤)
      r (by simp) f.toStrongDual b.val
    rw [WeightedCoeff.sobolevBilinearPairing_apply] at hh
    change (∑' n : ℤ, b.val.val n * (WeightedCoeff.weakStarCoeff r f).val (-n)) = f b.val at hh
    simpa only [WeightedCoeff.weakStarCoeff_val] using hh.symm
  have hs : star (f b.val) = f b.val := by
    rw [hr]
    change (starRingEnd ℂ) (∑' n : ℤ, b.val.val n * WeightedCoeff.weakStarCoordinates r f (-n)) = _
    rw [Complex.conj_tsum]
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ =>
      (starRingEnd ℂ) (b.val.val n * WeightedCoeff.weakStarCoordinates r f (-n)))]
    apply tsum_congr
    intro n
    simp only [Equiv.neg_apply, neg_neg, map_mul, b.property.2.1 n]
    change star (star (b.val.val n)) * star (WeightedCoeff.weakStarCoordinates r f n) = _
    rw [star_star, ← hf.1.2 n]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The actual original-distribution pairing on the actual real Wiener
predual is real valued, with the normalized physical action unchanged. -/
theorem originalRealWienerAction_im_zero (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hf : f ∈ potentialCoordinateLocus r) (u : OriginalRealWienerTest r) :
    ((coefficientWeakDualHomeomorph (L := 2) r f) u.val).im = 0 := by
  change (f (sobolevCoefficients r 1 u.val)).im = 0
  exact realWienerAction_im_zero r f hf ((realWienerTestOriginalEquiv r).symm u)

/-- The paper's real Wiener weak-star convergence criterion, for arbitrary
filters on every bounded source subset. -/
theorem tendsto_source_iff_originalRealWienerTests (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) (hA : A ⊆ potentialCoordinateLocus r)
    {X : Type*} {l : Filter X} (f : X → A) (a : A) :
    Tendsto f l (𝓝 a) ↔ ∀ u : OriginalRealWienerTest r,
      Tendsto (fun x => originalRealWienerEvaluations r (f x).val u) l
        (𝓝 (originalRealWienerEvaluations r a.val u)) := by
  rw [(isEmbedding_originalRealWienerEvaluations_on_bounded r A hb hA).tendsto_nhds_iff]
  exact tendsto_pi_nhds

end NLS.Articles.KdVPseudomeasures
