import NLS.ZakharovShabat.SourceSection20Original
import NLS.ZakharovShabat.SourceSection20Frequencies
import NLS.ZakharovShabat.SourceOrdinaryPhaseTrajectory
import NLS.SequenceSpaces.ShiftedHolderDecay

/-! # The ordinary frequency asymptotic with its physical mass limit

The exact original ordinary frequency differs from the free lattice by
four times mass and a sequence tending to zero in both signed directions.
This sharpens the introductory H1 O(1) assertion to every real FLp source
with 1 < p <= 2, and retains the actual constructed moment family.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)

omit [Fact (1 ≤ p)] in
private theorem halfExponent_le_two (hp2 : p ≤ 2) : ENNReal.ofReal (p.toReal/2) ≤ 2 := by
  have h : p.toReal ≤ (2 : ℝ) := by
    simpa using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hp2
  calc
    ENNReal.ofReal (p.toReal/2) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
    _ = 2 := by norm_num

include Q

/-- The original renormalized scalar frequencies vanish at both infinite ends. -/
theorem renormalizedFrequency_tendsto_zero (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    Tendsto (fun n : ℤ => A.renormalizedFrequency n φ.val) cofinite (𝓝 0) := by
  have he := (Q.sequence 2 (by simp) (by norm_num) (halfExponent_le_two hp2)).1
    φ.val (Q.real_subset φ.property)
  have ht := Coeff.tendsto_norm_apply_cofinite (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    (A.frequencySequence 2 φ.val)
  have hz : Tendsto (fun n : ℤ => A.frequencySequence 2 φ.val n) cofinite (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ht
  simpa only [he] using hz

/-- The precise mass shift is the limit of the ordinary frequency minus free dispersion. -/
theorem ordinaryFrequency_mass_limit (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    Tendsto (fun n : ℤ => A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2)
      cofinite (𝓝 (4*sourceOrdinaryMass hp2 φ)) := by
  have ht := (Complex.continuous_re.tendsto 0).comp (Q.renormalizedFrequency_tendsto_zero hp2 φ)
  have he (n : ℤ) : A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2 =
      (A.renormalizedFrequency n φ.val).re + 4*sourceOrdinaryMass hp2 φ := by
    simp only [SourceAbelianMomentAtlas.ordinaryPhaseFrequency]
    ring
  simp_rw [he]
  simpa using ht.add_const (4*sourceOrdinaryMass hp2 φ)

/-- An all-index bound for the literal ordinary O(1) remainder. -/
theorem ordinaryFrequency_remainder_bound (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    |A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2| ≤
      ‖A.frequencySequence 2 φ.val‖ + 4*|sourceOrdinaryMass hp2 φ| := by
  have he := (Q.sequence 2 (by simp) (by norm_num) (halfExponent_le_two hp2)).1
    φ.val (Q.real_subset φ.property) n
  have hn : |(A.renormalizedFrequency n φ.val).re| ≤ ‖A.frequencySequence 2 φ.val‖ := by
    rw [← he]
    exact (Complex.abs_re_le_norm _).trans (lp.norm_apply_le_norm (by norm_num) _ n)
  have hv : A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2 =
      (A.renormalizedFrequency n φ.val).re + 4*sourceOrdinaryMass hp2 φ := by
    simp only [SourceAbelianMomentAtlas.ordinaryPhaseFrequency]
    ring
  rw [hv]
  calc
    _ ≤ |(A.renormalizedFrequency n φ.val).re| + |4*sourceOrdinaryMass hp2 φ| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; norm_num; linarith

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat

/-- One constructed original family gives the exact ordinary asymptotic at every real source. -/
theorem exists_originalOrdinaryFrequency_mass_limit
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
    ∃ B U : Set (CoeffPair p), SourceSection20Data D A B U ∧
      ∀ φ : realTypeSourceSubmodule p,
        Tendsto (fun n : ℤ => A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2)
          cofinite (𝓝 (4*sourceOrdinaryMass hp2 φ)) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
          |A.ordinaryPhaseFrequency hp2 φ n - (2*Real.pi*n)^2| ≤ C := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  refine ⟨W₀,W,V,s,D,Wa,A,B,U,Q,?_⟩
  intro φ
  refine ⟨Q.ordinaryFrequency_mass_limit hp2 φ,
    ‖A.frequencySequence 2 φ.val‖+4*|sourceOrdinaryMass hp2 φ|+1,by positivity,?_⟩
  intro n
  exact (Q.ordinaryFrequency_remainder_bound hp2 φ n).trans (by linarith)

end NLS.ZakharovShabat
