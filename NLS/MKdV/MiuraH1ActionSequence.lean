import NLS.MKdV.MiuraSobolevActionSequence
import NLS.MKdV.MiuraActionFlowGroup

/-! # Original H1 physical actions in weighted l1 of order three

The entire original positive-index Hill action sequence has the native
weighted norm and an actual analytic extension on one complex H1
neighborhood of the entire real H1 space. The signed mean can be paired
with it. All coordinate identifications retain the physical factor 1/2.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSpectralActionWeight_one : miuraSpectralActionWeight 1 = Weight.sobolev 3 := by
  unfold miuraSpectralActionWeight
  norm_num

theorem miuraSobolevActionSource_one (a : ScalarDomain 2) :
    miuraSobolevActionSource 1 (miuraH1SobolevEquiv a) = miuraActionSourceCLM a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext j
    change (miuraSobolevActionSource 1 (miuraH1SobolevEquiv a)).fst j =
      (sobolevSourceInclusion (a,a)).fst j
    rw [miuraSobolevActionSource_fst,miuraH1SobolevEquiv_apply,sobolevSourceInclusion_fst]
  · ext j
    change (miuraSobolevActionSource 1 (miuraH1SobolevEquiv a)).snd j =
      (sobolevSourceInclusion (a,a)).snd j
    rw [miuraSobolevActionSource_snd,miuraH1SobolevEquiv_apply,sobolevSourceInclusion_snd]

def miuraH1ActionSequence (a : ScalarDomain 2) : WeightedCoeff (Weight.sobolev 3) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 3) 1).symm
    (miuraPositiveActionProjection (sourceWeightedZeroLaurentSequence (Weight.sobolev 3) miuraActionSourceCLM a))

def miuraH1ActionMeanMap (a : ScalarDomain 2) : WeightedCoeff (Weight.sobolev 3) 1 × ℂ :=
  (miuraH1ActionSequence a,a.val 0)

theorem exists_local_miuraH1ActionSequence_domain (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ U : Set (ScalarDomain 2), IsOpen U ∧ a ∈ U ∧ AnalyticOnNhd ℂ miuraH1ActionSequence U ∧
      ∀ b ∈ U, ∀ n : ℕ, 1 ≤ n → (miuraH1ActionSequence b).val (n : ℤ) = miuraComplexActionLevel n 1 b := by
  let T := sobolevSourceWeightedPeriodOne.comp
    ((ContinuousLinearMap.id ℂ (ScalarDomain 2)).prod (ContinuousLinearMap.id ℂ (ScalarDomain 2)))
  have hTL (b : ScalarDomain 2) : weightedBaseToPair (SpectralWeight.sobolev 1 (by norm_num)) (T b) =
      periodOnePotential (miuraActionSourceCLM b) := weightedBaseToPair_sobolevSourceWeightedPeriodOne (b,b)
  have hqw (n : ℤ) : Weight.sobolev 3 n/(1+|(n : ℝ)|) ≤ ((SpectralWeight.sobolev 1 (by norm_num)) (2*n))^2 := by
    simpa only [miuraSpectralActionWeight_one,Nat.cast_one] using! miuraSpectralActionWeight_gap_bound 1 n
  have hreal : miuraActionSourceCLM a ∈ realDiagonalSourceLocus 2 :=
    ⟨(realDiagonalH1Source a ha).property,rfl⟩
  obtain ⟨U,hU,haU,he,hA⟩ := exists_local_sourceWeightedZeroLaurentSequence_analytic
    (SpectralWeight.sobolev 1 (by norm_num)) (Weight.sobolev 3)
    (fun n => (Weight.sobolev 3).positive n |>.le) hqw miuraActionSourceCLM T hTL a hreal
  refine ⟨U,hU,haU,?_,?_⟩
  · intro b hb
    exact (((WeightedCoeff.weightIsometry (Weight.sobolev 3) 1).symm.toContinuousLinearEquiv.analyticAt _).comp
      ((miuraPositiveActionProjection.analyticAt _).comp (hA b hb)))
  · intro b hb n hn
    have hp : (0 : ℤ) < n := by omega
    change ((if (0 : ℤ) < n then (1/2 : ℂ) else 0)*sourceWeightedZeroLaurentSequence (Weight.sobolev 3) miuraActionSourceCLM b n)/
      (Weight.sobolev 3 n : ℂ) = _
    rw [if_pos hp,he b hb n,if_neg (ne_of_gt hp)]
    rw [miuraComplexActionLevel,show 2*(1 : ℤ)-2 = 0 by norm_num]
    calc
      _ = (Weight.sobolev 3 n : ℂ)*
          ((1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraActionSourceCLM b))/
            (Weight.sobolev 3 n : ℂ) := by ring
      _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 3).complex_ne_zero (n : ℤ))

theorem exists_miuraH1ActionSequence_domain :
    ∃ U : Set (ScalarDomain 2), IsOpen U ∧ {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ miuraH1ActionSequence U ∧
      ∀ b ∈ U, ∀ n : ℕ, 1 ≤ n → (miuraH1ActionSequence b).val (n : ℤ) = miuraComplexActionLevel n 1 b := by
  let R := {a : ScalarDomain 2 // ∀ j, a.val j = conj (a.val (-j))}
  have hlocal (a : R) := exists_local_miuraH1ActionSequence_domain a.val a.property
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

theorem miuraH1ActionSequence_physical (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraH1ActionSequence a).val (n : ℤ) = miuraMKdVAction a ha n := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraH1ActionSequence_domain
  rw [hcoord a (hreal ha) n hn,miuraComplexActionLevel_eq_real a ha n hn 1,miuraMKdVActionLevel_one]

theorem miuraH1ActionSequence_nonpositive (a : ScalarDomain 2) (n : ℤ) (hn : ¬ 0 < n) :
    (miuraH1ActionSequence a).val n = 0 := by
  change ((if 0 < n then (1/2 : ℂ) else 0)*sourceWeightedZeroLaurentSequence (Weight.sobolev 3) miuraActionSourceCLM a n)/
    (Weight.sobolev 3 n : ℂ) = 0
  rw [if_neg hn,zero_mul,zero_div]

theorem exists_miuraH1ActionMeanMap_domain :
    ∃ U : Set (ScalarDomain 2), IsOpen U ∧ {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ miuraH1ActionMeanMap U := by
  obtain ⟨U,hU,hreal,hA,_⟩ := exists_miuraH1ActionSequence_domain
  exact ⟨U,hU,hreal,fun a ha => (hA a ha).prod ((WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0).analyticAt a)⟩

theorem summable_weighted_physical_miuraActions (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Summable (fun n : ℕ => (1+((n : ℝ)+1))^3*‖miuraMKdVAction a ha (n+1)‖) := by
  have hs := (miuraH1ActionSequence a).property.norm.summable_of_one
  have ht := hs.comp_injective (i := fun n : ℕ => (n : ℤ)+1) (by intro m n h; dsimp only at h; omega)
  apply ht.congr
  intro n
  change ‖(Weight.sobolev 3 ((n : ℤ)+1) : ℂ)*(miuraH1ActionSequence a).val ((n : ℤ)+1)‖ = _
  rw [show (n : ℤ)+1 = ((n+1 : ℕ) : ℤ) by norm_num,
    miuraH1ActionSequence_physical a ha (n+1) (by omega),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev 3).positive _),
    Weight.sobolev_apply]
  norm_num [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)+1)]

end NLS.MKdV
