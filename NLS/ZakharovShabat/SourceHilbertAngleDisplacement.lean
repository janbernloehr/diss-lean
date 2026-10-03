import NLS.FunctionalAnalysis.IntegralDisplacement
import NLS.ZakharovShabat.SourceHilbertAngleStrongRegularity
import NLS.ZakharovShabat.SourceHilbertAngleFlowUnique
import Mathlib.Data.Real.ConjExponents

/-! # Lemma 17.4(ii): regularity of the angle-flow displacement

Integrate the actual angle vector in the conjugate exponent to recover
the source displacement below two. Above two, continuous inclusion of
the Hilbert displacement suffices. All conclusions concern the original
source Fourier coefficients and their full exponent norm.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Integration of the stronger angle vector recovers the full Hilbert
displacement through coefficient-preserving inclusion. -/
theorem hilbert_angleFlow_displacement_of_conjugate
    [p.HolderConjugate q] (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (hp2 : p ≤ 2) (h2q : 2 ≤ q)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    {A₀ H A : Set (CoeffPair q)} {w : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    (F : SourceAngularThetaCommonDomainData hq hq1 A₀ H A w)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ d : ℝ → CoeffPair p, d 0 = 0 ∧ ContinuousOn d (Iio a) ∧
      ∀ t < a, CoeffPair.exponentInclusion hp2 (d t) = (D.hilbertActionReduction φ k t).val-φ.val := by
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
  let f : ℝ → CoeffPair 2 := fun t => (D.hilbertActionReduction φ k t).val
  let v : ℝ → CoeffPair p := fun t => hilbertThetaVectorInExponent hp hq hq1 h2q k w (f t)
  have hfcont : Continuous f :=
    continuous_subtype_val.comp (D.continuous_hilbertActionReduction φ k)
  have hv : ContinuousOn v (Iio a) := by
    intro t ht
    exact ((F.analyticAt_hilbertThetaVectorInExponent h2q k
      (D.hilbertActionReduction φ k t) (D.hilbertActionReduction_gap_ne_zero k φ ha ht)).continuousAt.comp (f := f)
        hfcont.continuousAt).continuousWithinAt
  have hf : ∀ t < a, HasDerivAt f ((CoeffPair.exponentInclusion hp2) (v t)) t := by
    intro t ht
    have he := E.hilbertThetaVectorInExponent_inclusion (hp := hp) F hp2 h2q k
      (D.hilbertActionReduction φ k t) (D.hilbertActionReduction_gap_ne_zero k φ ha ht)
    change CoeffPair.exponentInclusion hp2 (v t) = _ at he
    rw [he]
    exact D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E k φ ha ht
  obtain ⟨d,hzero,hcont,_,hd⟩ := NLS.FunctionalAnalysis.exists_continuous_displacement_of_hasDerivAt
    ((CoeffPair.exponentInclusion hp2).restrictScalars ℝ) f v ha hv hf
  refine ⟨d,hzero,hcont,fun t ht => ?_⟩
  simpa only [f,D.hilbertActionReduction_zero] using! hd t ht

/-- Lemma 17.4(ii): at every finite exponent above one, the original
source displacement has a continuous real-type coefficient realization. -/
theorem hilbert_angleFlow_displacement_all_exponents
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ d : ℝ → CoeffPair p, d 0 = 0 ∧ ContinuousOn d (Iio a) ∧
      ∀ t < a, IsRealType (CoeffPair.toMax p (d t)) ∧ ∀ n : ℤ,
        (d t).fst n = (D.hilbertActionReduction φ k t).val.fst n-φ.val.fst n ∧
        (d t).snd n = (D.hilbertActionReduction φ k t).val.snd n-φ.val.snd n := by
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
  suffices ∃ d : ℝ → CoeffPair p, d 0 = 0 ∧ ContinuousOn d (Iio a) ∧ ∀ t < a, ∀ n : ℤ,
      (d t).fst n = (D.hilbertActionReduction φ k t).val.fst n-φ.val.fst n ∧
      (d t).snd n = (D.hilbertActionReduction φ k t).val.snd n-φ.val.snd n by
    obtain ⟨d,hzero,hcont,hd⟩ := this
    refine ⟨d,hzero,hcont,fun t ht => ⟨?_,hd t ht⟩⟩
    intro n
    change (d t).snd n = starRingEnd ℂ ((d t).fst (-n))
    rw [(hd t ht n).2,(hd t ht (-n)).1]
    exact (D.hilbertActionReduction φ k t-φ).property n
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · let d : ℝ → CoeffPair p := fun t => CoeffPair.exponentInclusion h2p
      ((D.hilbertActionReduction φ k t).val-φ.val)
    refine ⟨d,?_,?_,fun t _ n => ⟨rfl,rfl⟩⟩
    · simp [d,D.hilbertActionReduction_zero]
    · exact ((CoeffPair.exponentInclusion h2p).continuous.comp
        ((continuous_subtype_val.comp (D.continuous_hilbertActionReduction φ k)).sub continuous_const)).continuousOn
  · have hp2 : p ≤ 2 := le_of_not_ge h2p
    let q := ENNReal.conjExponent p
    have : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp1.le
    have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
    have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
    have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top
    have h2q : (2 : ℝ≥0∞) ≤ q := by
      apply ENNReal.inv_le_inv.mp
      calc
        q⁻¹ = 1-p⁻¹ := (ENNReal.HolderConjugate.one_sub_inv p q).symm
        _ ≤ 1-(2 : ℝ≥0∞)⁻¹ := tsub_le_tsub_left (ENNReal.inv_le_inv.mpr hp2) 1
        _ = (2 : ℝ≥0∞)⁻¹ := ENNReal.HolderConjugate.one_sub_inv 2 2
    obtain ⟨V₀,C,V,_,_,_,_,_,_,u,E⟩ :=
      exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
    obtain ⟨A₀,H,A,_,_,_,_,_,_,w,F⟩ := exists_sourceAngularTheta_theorem13_1_iv hq hq1
    obtain ⟨d,hzero,hcont,hd⟩ := D.hilbert_angleFlow_displacement_of_conjugate hp hq hq1 hp2 h2q E F k φ ha
    refine ⟨d,hzero,hcont,fun t ht n => ?_⟩
    exact ⟨congrArg (fun ψ : CoeffPair 2 => ψ.fst n) (hd t ht),
      congrArg (fun ψ : CoeffPair 2 => ψ.snd n) (hd t ht)⟩

/-- The displacement is continuous in the actual real source space,
not only as a collection of individual coefficient functions. -/
theorem hilbert_angleFlow_continuous_real_displacement
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ d : Iio a → realTypeSourceSubmodule p, Continuous d ∧ d ⟨0,ha⟩ = 0 ∧
      ∀ t : Iio a, ∀ n : ℤ,
        (d t).val.fst n = (D.hilbertActionReduction φ k t.val).val.fst n-φ.val.fst n ∧
        (d t).val.snd n = (D.hilbertActionReduction φ k t.val).val.snd n-φ.val.snd n := by
  obtain ⟨d,hzero,hcont,hd⟩ := D.hilbert_angleFlow_displacement_all_exponents hp hp1 k φ ha
  let e : Iio (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re → realTypeSourceSubmodule p :=
    fun t => ⟨d t.val,(hd t.val t.property).1⟩
  refine ⟨e,?_,Subtype.ext hzero,fun t n => (hd t.val t.property).2 n⟩
  exact hcont.domRestrict.subtype_mk _

/-- Lemma 17.4: the actual Hilbert angle flow exists uniquely up to the
initial selected action, that action tends to zero, and the source
displacement is continuous in every finite exponent above one. -/
theorem lemma17_4
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ f : ℝ → realTypeSourceSubmodule 2,
      f 0 = φ ∧ ContDiffOn ℝ 1 f (Iio a) ∧
      (∀ t < a, HasDerivAt (fun t => (f t).val)
        (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u (f t).val) t) ∧
      (∀ g : ℝ → CoeffPair 2, g 0 = φ.val →
        (∀ t < a, HasDerivAt g
          (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u (g t)) t) →
        EqOn g (fun t => (f t).val) (Iio a)) ∧
      Tendsto (fun t => (sourceRealAction (by simp) (by norm_num) (f t).val (f t).property k).re)
        (𝓝[<] a) (𝓝 0) ∧
      ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
        ∃ d : Iio a → realTypeSourceSubmodule r, Continuous d ∧ ∀ t : Iio a, ∀ n : ℤ,
          (d t).val.fst n = (f t.val).val.fst n-φ.val.fst n ∧
          (d t).val.snd n = (f t.val).val.snd n-φ.val.snd n := by
  have ha := hilbert_action_pos_of_gap_ne_zero φ k hk
  refine ⟨D.hilbertActionReduction φ k,D.hilbertActionReduction_zero φ k,?_,
    fun t ht => D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E k φ ha ht,
    fun g hzero hg => D.hilbertActionReduction_thetaHamiltonian_unique E k φ ha g hzero hg,
    D.tendsto_action_hilbertActionReduction φ k ha,?_⟩
  · intro t ht
    exact ((D.contDiffAt_hilbertActionReduction φ k ha ht).of_le (by simp)).contDiffWithinAt
  · intro r _ hr hr1
    obtain ⟨d,hcont,_,hd⟩ := D.hilbert_angleFlow_continuous_real_displacement hr hr1 k φ ha
    exact ⟨d,hcont,hd⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
