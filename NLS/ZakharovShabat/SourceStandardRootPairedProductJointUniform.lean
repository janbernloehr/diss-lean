import NLS.ZakharovShabat.SourceStandardRootPairedProductHolomorphic
import NLS.ZakharovShabat.SourceStandardRootPairedProductAnalytic
import NLS.SequenceSpaces.UniformHolderTails

/-!
# Source-uniform tails for the paired standard-root product

The midpoint part of the product is a bounded family of Hölder products
with one fixed punctured reciprocal lattice. Its finite absolute sums
have a common bound and its high-frequency tails vanish uniformly near
each source potential. This is the source-dependent piece of joint product
convergence in Lemma 10.5.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A source neighborhood has a uniform absolute-sum bound for midpoint
corrections, with a tail bound tending to zero for every finite index set. -/
theorem exists_uniform_absolute_sourceStandardRootMidpointCorrection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∃ D : ℕ → ℝ, Tendsto D atTop (𝓝 0) ∧
        (∀ ψ ∈ V, ∀ s : Finset ℤ,
          (∑ k ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ k‖) ≤ B) ∧
        (∀ N : ℕ, ∀ ψ ∈ V, ∀ s : Finset ℤ,
          (∀ k ∈ s, N ≤ k.natAbs) →
          (∑ k ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ k‖) ≤ D N) := by
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hqtop : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let b := Coeff.puncturedLattice p.conjExponent hq
  let C : ℝ := ‖(Real.pi : ℂ)⁻¹‖
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨_, _, V, hVopen, hφV, R, hR, hdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  have h := Coeff.uniform_absolute_holder_tails
    (fun ψ : CoeffPair p => sourcePeriodicMidpointDisplacement hp hp1 ψ)
    b hqtop
    (fun ψ k => sourceStandardRootMidpointCorrection hp hp1 ψ k)
    V C R hC
    (fun ψ hψ => (hdata ψ hψ).1)
    (fun ψ _ k => by
      change ‖((Real.pi : ℂ)⁻¹ •
        Coeff.holderProduct (q := 1)
          (sourcePeriodicMidpointDisplacement hp hp1 ψ) b) k‖ ≤
        C * ‖sourcePeriodicMidpointDisplacement hp hp1 ψ k * b k‖
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        Coeff.holderProduct_apply, norm_mul]
      rfl)
  exact ⟨V, hVopen, hφV, C*R*‖b‖, by positivity,
    (fun N => C*R*‖Coeff.fourierTail N b‖), h.2.1, h.1, h.2.2⟩

/-- The two midpoint corrections in every positive-index pair have
uniformly bounded finite absolute sums and uniformly vanishing tails. -/
theorem exists_uniform_absolute_sourceStandardRootPairedMidpointCorrection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∃ D : ℕ → ℝ, Tendsto D atTop (𝓝 0) ∧
        (∀ ψ ∈ V, ∀ s : Finset ℕ,
          (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ
              (((j+1 : ℕ) : ℤ)) +
            sourceStandardRootMidpointCorrection hp hp1 ψ
              (-((j+1 : ℕ) : ℤ))‖) ≤ B) ∧
        (∀ N : ℕ, ∀ ψ ∈ V, ∀ s : Finset ℕ,
          (∀ j ∈ s, N ≤ j) →
          (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ
              (((j+1 : ℕ) : ℤ)) +
            sourceStandardRootMidpointCorrection hp hp1 ψ
              (-((j+1 : ℕ) : ℤ))‖) ≤ D N) := by
  obtain ⟨V, hVopen, hφV, B, hB, D, hD, hbound, htail⟩ :=
    exists_uniform_absolute_sourceStandardRootMidpointCorrection hp hp1 φ
  let fpos : ℕ → ℤ := fun j => ((j+1 : ℕ) : ℤ)
  let fneg : ℕ → ℤ := fun j => -((j+1 : ℕ) : ℤ)
  have hfpos : Function.Injective fpos := by
    intro i j hij
    have := Int.ofNat_injective hij
    omega
  have hfneg : Function.Injective fneg := by
    intro i j hij
    exact hfpos (neg_injective hij)
  have hsum (ψ : CoeffPair p) (s : Finset ℕ) :
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fpos j) +
        sourceStandardRootMidpointCorrection hp hp1 ψ (fneg j)‖) ≤
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fpos j)‖) +
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fneg j)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => norm_add_le _ _)
  have hpos (ψ : CoeffPair p) (hψ : ψ ∈ V) (s : Finset ℕ) :
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fpos j)‖) ≤ B := by
    have h := hbound ψ hψ (s.image fpos)
    rw [Finset.sum_image (fun i _ j _ hij => hfpos hij)] at h
    exact h
  have hneg (ψ : CoeffPair p) (hψ : ψ ∈ V) (s : Finset ℕ) :
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fneg j)‖) ≤ B := by
    have h := hbound ψ hψ (s.image fneg)
    rw [Finset.sum_image (fun i _ j _ hij => hfneg hij)] at h
    exact h
  have hposTail (N : ℕ) (ψ : CoeffPair p) (hψ : ψ ∈ V)
      (s : Finset ℕ) (hs : ∀ j ∈ s, N ≤ j) :
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fpos j)‖) ≤ D N := by
    have h := htail N ψ hψ (s.image fpos) (by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hNj := hs j hj
      dsimp [fpos]
      omega)
    rw [Finset.sum_image (fun i _ j _ hij => hfpos hij)] at h
    exact h
  have hnegTail (N : ℕ) (ψ : CoeffPair p) (hψ : ψ ∈ V)
      (s : Finset ℕ) (hs : ∀ j ∈ s, N ≤ j) :
      (∑ j ∈ s, ‖sourceStandardRootMidpointCorrection hp hp1 ψ (fneg j)‖) ≤ D N := by
    have h := htail N ψ hψ (s.image fneg) (by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hNj := hs j hj
      dsimp [fneg]
      simp only [Int.natAbs_neg]
      omega)
    rw [Finset.sum_image (fun i _ j _ hij => hfneg hij)] at h
    exact h
  refine ⟨V, hVopen, hφV, 2*B, by positivity,
    (fun N => 2*D N), by simpa using tendsto_const_nhds.mul hD, ?_, ?_⟩
  · intro ψ hψ s
    dsimp only [fpos, fneg] at hsum hpos hneg
    linarith [hsum ψ s, hpos ψ hψ s, hneg ψ hψ s]
  · intro N ψ hψ s hs
    dsimp only [fpos, fneg] at hsum hposTail hnegTail
    linarith [hsum ψ s, hposTail N ψ hψ s hs, hnegTail N ψ hψ s hs]

/-- Near a source potential, on a bounded spectral region, the complete
paired-factor errors have uniformly vanishing finite absolute tails. -/
theorem exists_uniform_absolute_sourceStandardRootPairedFactor_tails
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ N₀ : ℕ, ∃ D : ℕ → ℝ, Tendsto D atTop (𝓝 0) ∧
        ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ V, ∀ z : ℂ, ‖z‖ ≤ R →
          ∀ s : Finset ℕ, (∀ j ∈ s, N ≤ j) →
            (∑ j ∈ s, ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖) ≤ D N := by
  obtain ⟨V₁, hV₁open, hφ₁, _, _, D₁, hD₁, _, hmid⟩ :=
    exists_uniform_absolute_sourceStandardRootPairedMidpointCorrection hp hp1 φ
  obtain ⟨N₂, V₂, C, hV₂open, hφ₂, hC, hsqrt, _⟩ :=
    exists_uniform_sourceStandardRootSqrtCorrection_majorant hp hp1 φ R
  obtain ⟨N₃, V₃, A, hV₃open, hφ₃, hA, hcross, _⟩ :=
    exists_uniform_sourceStandardRootPairedCross_majorant hp hp1 φ R hR
  let q : ℕ → ℝ := fun j => 1/((j : ℝ)+1)^2
  have hq : Summable q := by
    dsimp [q]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let E : ℕ → ℝ := fun N => ∑' j : ℕ, if N ≤ j then q j else 0
  have hEq (N : ℕ) :
      (∑' j : {x : ℕ // x ∉ Finset.range N}, q j) = E N := by
    calc
      _ = ∑' j : ℕ, ({x : ℕ | x ∉ Finset.range N} : Set ℕ).indicator q j :=
        tsum_subtype _ _
      _ = E N := by
        dsimp [E]
        congr 1
        funext j
        by_cases hj : N ≤ j <;> simp [Set.indicator, Finset.mem_range, hj]
  have hE : Tendsto E atTop (𝓝 0) := by
    convert (tendsto_tsum_compl_atTop_zero q).comp tendsto_finset_range using 1
    funext N
    exact (hEq N).symm
  let D : ℕ → ℝ := fun N => D₁ N + (2*C+A)*E N
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [D, zero_add, mul_zero] using
      hD₁.add (tendsto_const_nhds.mul hE)
  refine ⟨V₁ ∩ V₂ ∩ V₃,
    (hV₁open.inter hV₂open).inter hV₃open,
    ⟨⟨hφ₁, hφ₂⟩, hφ₃⟩, max N₂ N₃, D, hD, ?_⟩
  intro N hN ψ hψ z hz s hs
  have hψ₁ : ψ ∈ V₁ := hψ.1.1
  have hψ₂ : ψ ∈ V₂ := hψ.1.2
  have hψ₃ : ψ ∈ V₃ := hψ.2
  have hpoint (j : ℕ) (hj : j ∈ s) :
      ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖ ≤
        ‖sourceStandardRootMidpointCorrection hp hp1 ψ (((j+1 : ℕ) : ℤ)) +
          sourceStandardRootMidpointCorrection hp hp1 ψ (-((j+1 : ℕ) : ℤ))‖ +
        (2*C+A)*q j := by
    let k : ℤ := ((j+1 : ℕ) : ℤ)
    have hjN := hs j hj
    have hk₂ : N₂ < k.natAbs := by dsimp [k]; omega
    have hk₃ : N₃ < k.natAbs := by dsimp [k]; omega
    have hrpos := hsqrt ψ hψ₂ z hz k hk₂
    have hrneg := hsqrt ψ hψ₂ z hz (-k) (by simpa using hk₂)
    have hcross' := hcross ψ hψ₃ z hz k hk₃
    have hpow : |(k : ℝ)| ^ (-(2 : ℝ)) = q j := by
      have hkpos : 0 < |(k : ℝ)| := by dsimp [k]; positivity
      rw [Real.rpow_neg hkpos.le, Real.rpow_ofNat]
      simp [q, k, Nat.cast_add, Nat.cast_one]
    rw [hpow] at hrpos hcross'
    have hrneg' : ‖sourceStandardRootSqrtCorrection hp hp1 ψ z (-k)‖ ≤ C*q j := by
      simpa only [Int.cast_neg, abs_neg, hpow] using hrneg
    rw [sourceStandardRootPairedFactor_sub_one_eq_corrections]
    have ht₁ := norm_add_le
      (sourceStandardRootMidpointCorrection hp hp1 ψ k +
        sourceStandardRootMidpointCorrection hp hp1 ψ (-k) +
        sourceStandardRootSqrtCorrection hp hp1 ψ z k +
        sourceStandardRootSqrtCorrection hp hp1 ψ z (-k))
      (sourceStandardRootRelativeError hp hp1 ψ k z *
        sourceStandardRootRelativeError hp hp1 ψ (-k) z)
    have ht₂ := norm_add_le
      (sourceStandardRootMidpointCorrection hp hp1 ψ k +
        sourceStandardRootMidpointCorrection hp hp1 ψ (-k) +
        sourceStandardRootSqrtCorrection hp hp1 ψ z k)
      (sourceStandardRootSqrtCorrection hp hp1 ψ z (-k))
    have ht₃ := norm_add_le
      (sourceStandardRootMidpointCorrection hp hp1 ψ k +
        sourceStandardRootMidpointCorrection hp hp1 ψ (-k))
      (sourceStandardRootSqrtCorrection hp hp1 ψ z k)
    dsimp only [k] at *
    nlinarith
  have hsum := Finset.sum_le_sum (fun j hj => hpoint j hj)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hmid' := hmid N ψ hψ₁ s hs
  have hqnonneg (j : ℕ) : 0 ≤ q j := by dsimp [q]; positivity
  have hE_summable : Summable (fun j : ℕ => if N ≤ j then q j else 0) := by
    apply hq.of_nonneg_of_le
    · intro j; split_ifs <;> positivity
    · intro j; split_ifs <;> simp [hqnonneg j]
  have hqtail : (∑ j ∈ s, q j) ≤ E N := by
    calc
      _ = ∑ j ∈ s, (if N ≤ j then q j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [hs j hj]
      _ ≤ E N := hE_summable.sum_le_tsum s (fun j _ => by split_ifs <;> positivity)
  have hCA : 0 ≤ 2*C+A := by positivity
  dsimp only [D]
  nlinarith [mul_le_mul_of_nonneg_left hqtail hCA]

set_option maxHeartbeats 1000000

/-- The paired factor as a function of the spectral point and source. -/
def sourceStandardRootPairedJointFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (j : ℕ) : ℂ × CoeffPair p → ℂ :=
  fun t => sourceStandardRootPairedFactor hp hp1 t.2 t.1 j

/-- The finite paired cutoff as a joint function. -/
def sourceStandardRootPairedJointPartialProduct (hp : p ≠ ⊤)
    (hp1 : 1 < p) (N : ℕ) : ℂ × CoeffPair p → ℂ :=
  fun t => sourceStandardRootPairedPartialProduct hp hp1 t.2 t.1 N

/-- The infinite paired product as a joint function. -/
def sourceStandardRootPairedJointProduct (hp : p ≠ ⊤)
    (hp1 : 1 < p) : ℂ × CoeffPair p → ℂ :=
  fun t => sourceStandardRootPairedProduct hp hp1 t.2 t.1

/-- Joint continuity of finite cutoffs at one source/spectral point and
the uniform factor tails give uniform product convergence on a joint
neighborhood of that point. -/
theorem exists_local_uniform_sourceStandardRootPairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ)
    (hcont : ∀ N : ℕ, ContinuousAt
      (sourceStandardRootPairedJointPartialProduct hp hp1 N) (z,φ)) :
    ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
      TendstoUniformlyOn (sourceStandardRootPairedJointPartialProduct hp hp1)
        (sourceStandardRootPairedJointProduct hp hp1)
        atTop U := by
  let R : ℝ := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨V, hVopen, hφV, N₀, D, hD, htail⟩ :=
    exists_uniform_absolute_sourceStandardRootPairedFactor_tails hp hp1 φ R hR
  let F : ℂ × CoeffPair p → ℂ := sourceStandardRootPairedJointPartialProduct hp hp1 N₀
  have hFcont : ContinuousAt F (z,φ) := hcont N₀
  let P : ℝ := ‖F (z,φ)‖+1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hFP : ‖F (z,φ)‖ < P := by dsimp [P]; linarith
  have hnear : {t : ℂ × CoeffPair p | ‖F t‖ < P} ∈ 𝓝 (z,φ) :=
    hFcont.norm (gt_mem_nhds hFP)
  obtain ⟨U₁, hU₁sub, hU₁open, hbaseU₁⟩ := _root_.mem_nhds_iff.mp hnear
  let U : Set (ℂ × CoeffPair p) :=
    U₁ ∩ {t | t.2 ∈ V} ∩ {t | ‖t.1‖ < R}
  have hUopen : IsOpen U := by
    exact (hU₁open.inter (hVopen.preimage continuous_snd)).inter
      (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
  have hbaseU : (z,φ) ∈ U := by
    refine ⟨⟨hbaseU₁, hφV⟩, ?_⟩
    dsimp [R]
    linarith
  have hfac (t : ℂ × CoeffPair p) (j : ℕ) :
      1 + (sourceStandardRootPairedFactor hp hp1 t.2 t.1 j - 1) =
        sourceStandardRootPairedFactor hp hp1 t.2 t.1 j := by ring
  have hfinite (t : ℂ × CoeffPair p) (N : ℕ) :
      (∏ j ∈ Finset.range N,
        (1 + (sourceStandardRootPairedJointFactor hp hp1 j t - 1))) =
          sourceStandardRootPairedJointPartialProduct hp hp1 N t := by
    change (∏ j ∈ Finset.range N,
        (1 + (sourceStandardRootPairedFactor hp hp1 t.2 t.1 j - 1))) =
      ∏ j ∈ Finset.range N, sourceStandardRootPairedFactor hp hp1 t.2 t.1 j
    apply Finset.prod_congr rfl
    intro j _
    exact hfac t j
  have hprod := NLS.ComplexAnalysis.tendstoUniformlyOn_prod_one_add_nat_of_tail
    (fun t j => sourceStandardRootPairedJointFactor hp hp1 j t - 1)
    U N₀ P hP
    (fun t ht => by
      have hpre : ‖F t‖ < P := hU₁sub ht.1.1
      rw [hfinite]
      exact hpre.le)
    D hD
    (fun N hN t ht s hs =>
      htail N hN t.2 ht.1.2 t.1 ht.2.le s hs)
    (sourceStandardRootPairedJointProduct hp hp1)
    (fun t _ => by
      have ht := tendsto_sourceStandardRootPairedPartialProduct hp hp1 t.2 t.1
      change Tendsto (fun N => ∏ j ∈ Finset.range N,
        (1 + (sourceStandardRootPairedJointFactor hp hp1 j t - 1))) atTop
          (𝓝 (sourceStandardRootPairedProduct hp hp1 t.2 t.1))
      have heq : (fun N => ∏ j ∈ Finset.range N,
        (1 + (sourceStandardRootPairedJointFactor hp hp1 j t - 1))) =
          (fun N => sourceStandardRootPairedPartialProduct hp hp1 t.2 t.1 N) := by
        funext N
        exact hfinite t N
      rw [heq]
      exact ht)
  refine ⟨U, hUopen, hbaseU, ?_⟩
  have hfun : (fun N t => ∏ j ∈ Finset.range N,
      (1 + (sourceStandardRootPairedJointFactor hp hp1 j t - 1))) =
      sourceStandardRootPairedJointPartialProduct hp hp1 := by
    funext N t
    exact hfinite t N
  rw [hfun] at hprod
  exact hprod

/-- The jointly uniform limit is continuous at any point where all its
finite cutoffs are jointly continuous. -/
theorem sourceStandardRootPairedJointProduct_continuousAt_of_finite
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ)
    (hcont : ∀ N : ℕ, ContinuousAt
      (sourceStandardRootPairedJointPartialProduct hp hp1 N) (z,φ)) :
    ContinuousAt (sourceStandardRootPairedJointProduct hp hp1) (z,φ) := by
  obtain ⟨U, hUopen, hxU, hconv⟩ :=
    exists_local_uniform_sourceStandardRootPairedProduct hp hp1 φ z hcont
  apply continuousAt_of_locally_uniform_approx_of_continuousAt
  intro u hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv u hu)
  exact ⟨U, hUopen.mem_nhds hxU,
    sourceStandardRootPairedJointPartialProduct hp hp1 N, hcont N,
    fun t ht => hN N le_rfl t ht⟩

/-- On the connected source neighborhood with jointly analytic finite
cutoffs, the paired product converges locally uniformly in both the
spectral point and source at every point of its natural domain. -/
theorem exists_global_source_locally_uniform_pairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ z ∈ sourceStandardRootPairedDomain hp hp1 φ,
        ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
          TendstoUniformlyOn (sourceStandardRootPairedJointPartialProduct hp hp1)
            (sourceStandardRootPairedJointProduct hp hp1) atTop U := by
  obtain ⟨W, hWopen, hWconnected, hreal, hanalytic⟩ :=
    exists_global_source_analytic_pairedPartialProduct hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro φ hφ z hz
  apply exists_local_uniform_sourceStandardRootPairedProduct hp hp1 φ z
  intro N
  exact (hanalytic φ hφ z hz N).continuousAt

/-- The omitted-zero paired product is jointly continuous at every
point of the common analytic source domain away from the noncentral gaps. -/
theorem exists_global_source_jointContinuous_pairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ z ∈ sourceStandardRootPairedDomain hp hp1 φ,
        ContinuousAt (sourceStandardRootPairedJointProduct hp hp1) (z,φ) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hanalytic⟩ :=
    exists_global_source_analytic_pairedPartialProduct hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro φ hφ z hz
  apply sourceStandardRootPairedJointProduct_continuousAt_of_finite hp hp1 φ z
  intro N
  exact (hanalytic φ hφ z hz N).continuousAt

/-- Joint continuity of the infinite product on the full common
source/gap-complement locus, viewed as a subspace. -/
theorem exists_global_source_continuousOn_pairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ContinuousOn (sourceStandardRootPairedJointProduct hp hp1)
        {t : ℂ × CoeffPair p |
          t.2 ∈ W ∧ t.1 ∈ sourceStandardRootPairedDomain hp hp1 t.2} := by
  obtain ⟨W, hWopen, hWconnected, hreal, hcont⟩ :=
    exists_global_source_jointContinuous_pairedProduct hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro t ht
  exact (hcont t.2 ht.1 t.1 ht.2).continuousWithinAt

/-- A nonzero paired product value persists on a joint neighborhood
whenever the product is continuous at that spectral/source point. -/
theorem exists_local_sourceStandardRootPairedJointProduct_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 φ)
    (hcont : ContinuousAt (sourceStandardRootPairedJointProduct hp hp1) (z,φ)) :
    ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
      ∀ t ∈ U, sourceStandardRootPairedJointProduct hp hp1 t ≠ 0 := by
  have hnonzero : sourceStandardRootPairedJointProduct hp hp1 (z,φ) ≠ 0 :=
    sourceStandardRootPairedProduct_ne_zero hp hp1 φ z hz
  have hnear : (sourceStandardRootPairedJointProduct hp hp1) ⁻¹'
      ({0}ᶜ : Set ℂ) ∈ 𝓝 (z,φ) :=
    hcont (isClosed_singleton.isOpen_compl.mem_nhds hnonzero)
  obtain ⟨U, hUsub, hUopen, hbaseU⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨U, hUopen, hbaseU, ?_⟩
  intro t ht
  exact hUsub ht

/-- On the common connected source domain, every point outside the
noncentral gaps has a joint neighborhood where the infinite paired
product remains nonzero. -/
theorem exists_global_source_localNonzero_pairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ z ∈ sourceStandardRootPairedDomain hp hp1 φ,
        ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
          ∀ t ∈ U, sourceStandardRootPairedJointProduct hp hp1 t ≠ 0 := by
  obtain ⟨W, hWopen, hWconnected, hreal, hcont⟩ :=
    exists_global_source_jointContinuous_pairedProduct hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro φ hφ z hz
  exact exists_local_sourceStandardRootPairedJointProduct_ne_zero
    hp hp1 φ z hz (hcont φ hφ z hz)

end NLS.ZakharovShabat
