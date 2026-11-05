import NLS.MKdV.MiuraActionMoment
import NLS.ZakharovShabat.SourceWeightedPeriodOne

/-! # The original L² physical action sequence

A direct unit-weight source realization gives the full analytic sequence
in weighted l1 of order one. Every positive coordinate is the actual
Laurent action extension, and the first moment agrees with the physical
H¹ trace on unchanged original coefficients.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraL2ActionSequence (a : Coeff 2) : WeightedCoeff (Weight.sobolev 1) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm
    (miuraPositiveActionProjection (sourceWeightedZeroLaurentSequence (Weight.sobolev 1) scalarL2Diagonal a))

theorem exists_local_miuraL2ActionSequence_domain (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ a ∈ U ∧ AnalyticOnNhd ℂ miuraL2ActionSequence U ∧
      (∀ b ∈ U, ∀ n : ℕ, 1 ≤ n → (miuraL2ActionSequence b).val (n : ℤ) = miuraL2Action n b) := by
  let T := sourceWeightedPeriodOne.toContinuousLinearMap.comp scalarL2Diagonal
  have hTL (b : Coeff 2) : weightedBaseToPair SpectralWeight.one (T b) =
      periodOnePotential (scalarL2Diagonal b) := weightedBaseToPair_sourceWeightedPeriodOne (scalarL2Diagonal b)
  have hqw (n : ℤ) : Weight.sobolev 1 n/(1+|(n : ℝ)|) ≤ (SpectralWeight.one (2*n))^2 := by
    simp [Weight.sobolev_apply,show (1+|(n : ℝ)|) ≠ 0 by positivity]
  have hreal : scalarL2Diagonal a ∈ realDiagonalSourceLocus 2 := by
    constructor
    · intro j
      change (scalarL2Diagonal a).snd j = conj ((scalarL2Diagonal a).fst (-j))
      rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
      exact ha j
    · rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
  obtain ⟨U,hU,haU,he,hA⟩ := exists_local_sourceWeightedZeroLaurentSequence_analytic
    SpectralWeight.one (Weight.sobolev 1)
    (fun n => (Weight.sobolev 1).positive n |>.le) hqw scalarL2Diagonal T hTL a hreal
  refine ⟨U,hU,haU,?_,?_⟩
  · intro b hb
    exact (((WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm.toContinuousLinearEquiv.analyticAt _).comp
      ((miuraPositiveActionProjection.analyticAt _).comp (hA b hb)))
  · intro b hb n hn
    have hp : (0 : ℤ) < n := by omega
    change ((if (0 : ℤ) < n then (1/2 : ℂ) else 0)*sourceWeightedZeroLaurentSequence (Weight.sobolev 1) scalarL2Diagonal b n)/
      (Weight.sobolev 1 n : ℂ) = _
    rw [if_pos hp,he b hb n,if_neg (ne_of_gt hp),miuraL2Action]
    calc
      _ = (Weight.sobolev 1 n : ℂ)*
          ((1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (scalarL2Diagonal b))/
            (Weight.sobolev 1 n : ℂ) := by ring
      _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero (n : ℤ))

theorem exists_miuraL2ActionSequence_domain :
    ∃ U : Set (Coeff 2), IsOpen U ∧ {a | ∀ j, a j = conj (a (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ miuraL2ActionSequence U ∧
      (∀ b ∈ U, ∀ n : ℕ, 1 ≤ n → (miuraL2ActionSequence b).val (n : ℤ) = miuraL2Action n b) := by
  let R := {a : Coeff 2 // ∀ j, a j = conj (a (-j))}
  have hlocal (a : R) := exists_local_miuraL2ActionSequence_domain a.val a.property
  choose V hV haV hA hcoord using hlocal
  refine ⟨⋃ a : R, V a,isOpen_iUnion hV,?_,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact hA a b ha
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact hcoord a b ha

theorem miuraL2ActionSequence_nonpositive (a : Coeff 2) (n : ℤ) (hn : ¬0 < n) :
    (miuraL2ActionSequence a).val n = 0 := by
  change ((if 0 < n then (1/2 : ℂ) else 0)*sourceWeightedZeroLaurentSequence (Weight.sobolev 1) scalarL2Diagonal a n)/
    (Weight.sobolev 1 n : ℂ) = 0
  rw [if_neg hn,zero_mul,zero_div]

private theorem miuraL2ActionMoment_symbol_bound (n : ℤ) :
    Weight.one n*‖2*(Real.pi : ℂ)*n‖ ≤ (2*Real.pi)*Weight.sobolev 1 n := by
  simp only [Weight.one_apply,one_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast,
    Weight.sobolev_apply,Real.rpow_one]
  nlinarith [Real.pi_pos]

def miuraL2ActionMomentSequence : WeightedCoeff (Weight.sobolev 1) 1 →L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry Weight.one 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM (Weight.sobolev 1) Weight.one
      (fun n => 2*(Real.pi : ℂ)*n) (2*Real.pi) (by positivity) miuraL2ActionMoment_symbol_bound)

theorem miuraL2ActionMomentSequence_apply (a : WeightedCoeff (Weight.sobolev 1) 1) (n : ℤ) :
    miuraL2ActionMomentSequence a n = (2*(Real.pi : ℂ)*n)*a.val n := by
  change (1 : ℂ)*((2*(Real.pi : ℂ)*n)*a.val n) = _
  exact one_mul _

def miuraL2ActionMomentFunctional : WeightedCoeff (Weight.sobolev 1) 1 →L[ℂ] ℂ :=
  (lp.tsumCLM ℂ ℤ ℂ).comp miuraL2ActionMomentSequence

def miuraL2ActionMoment (a : Coeff 2) : ℂ :=
  miuraL2ActionMomentFunctional (miuraL2ActionSequence a)

theorem analyticAt_miuraL2ActionMoment (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraL2ActionMoment a := by
  obtain ⟨U,_,hreal,hA,_⟩ := exists_miuraL2ActionSequence_domain
  exact ((lp.tsumCLM ℂ ℤ ℂ).analyticAt _).comp
    ((miuraL2ActionMomentSequence.analyticAt _).comp (hA a (hreal ha)))

theorem miuraL2ActionMoment_original_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraL2ActionMoment (scalarInclusion a) = miuraH1ActionMoment a := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  have haL2 : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have he : miuraL2ActionMomentSequence (miuraL2ActionSequence (scalarInclusion a)) =
      miuraActionMomentSequence (miuraH1ActionSequence a) := by
    ext n
    rw [miuraL2ActionMomentSequence_apply,miuraActionMomentSequence_apply]
    by_cases hn : 0 < n
    · have hnat : 1 ≤ n.toNat := by omega
      have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      rw [← hi,hcoord _ (hreal haL2) n.toNat hnat,
        miuraL2Action_eq_physical a ha n.toNat hnat,miuraH1ActionSequence_physical a ha n.toNat hnat]
    · rw [miuraL2ActionSequence_nonpositive _ n hn,miuraH1ActionSequence_nonpositive a n hn]
  exact congrArg (lp.tsumCLM ℂ ℤ ℂ) he

def miuraL2ActionMeanMap (a : Coeff 2) : WeightedCoeff (Weight.sobolev 1) 1 × ℂ :=
  (miuraL2ActionSequence a,a 0)

theorem analyticAt_miuraL2ActionMeanMap (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraL2ActionMeanMap a := by
  obtain ⟨U,_,hreal,hA,_⟩ := exists_miuraL2ActionSequence_domain
  exact (hA a (hreal ha)).prod ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt a)

end NLS.MKdV
