import NLS.MKdV.MiuraH1ActionSequence

/-! # Exact compatibility with the article's action-space topology

The article's squared Birkhoff weight is 1+|n|^(2s+1). The constructed
action space uses (1+|n|)^(2s+1). Explicit comparison bounds give a
coefficient-preserving continuous linear equivalence, retaining both
original topologies rather than merely an abstract sequence isomorphism.
-/
noncomputable section
open Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraPaperActionWeight (s : ℕ) : Weight :=
  ⟨fun n => 1+|(n : ℝ)|^(2*s+1),fun n => by positivity⟩

theorem miuraActionWeight_comparison (s : ℕ) (n : ℤ) :
    miuraPaperActionWeight s n ≤ miuraSpectralActionWeight s n ∧
      miuraSpectralActionWeight s n ≤ (2 : ℝ)^(2*s)*miuraPaperActionWeight s n := by
  change 1+|(n : ℝ)|^(2*s+1) ≤ (Weight.sobolev ((2*s+1 : ℕ) : ℝ)) n ∧ _
  simp only [Weight.sobolev_apply,Real.rpow_natCast]
  constructor
  · simpa only [one_pow] using pow_add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (abs_nonneg (n : ℝ)) (by omega : (2*s+1 : ℕ) ≠ 0)
  · simpa only [miuraSpectralActionWeight,Weight.sobolev_apply,Real.rpow_natCast,
      miuraPaperActionWeight,one_pow,show 2*s+1-1 = 2*s by omega] using
      add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg (n : ℝ)) (2*s+1)

def miuraActionToPaper (s : ℕ) :
    WeightedCoeff (miuraSpectralActionWeight s) 1 →L[ℂ] WeightedCoeff (miuraPaperActionWeight s) 1 :=
  WeightedCoeff.inclusionCLM _ _ (fun n => (miuraActionWeight_comparison s n).1)

def miuraActionFromPaper (s : ℕ) :
    WeightedCoeff (miuraPaperActionWeight s) 1 →L[ℂ] WeightedCoeff (miuraSpectralActionWeight s) 1 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) ((2 : ℝ)^(2*s)) (by positivity)
    (by intro n; simpa only [norm_one,mul_one] using (miuraActionWeight_comparison s n).2)

def miuraActionTopologyEquiv (s : ℕ) :
    WeightedCoeff (miuraSpectralActionWeight s) 1 ≃L[ℂ] WeightedCoeff (miuraPaperActionWeight s) 1 :=
  ContinuousLinearEquiv.equivOfInverse (miuraActionToPaper s) (miuraActionFromPaper s)
    (by intro a; apply Subtype.ext; funext n; simp [miuraActionToPaper,miuraActionFromPaper])
    (by intro a; apply Subtype.ext; funext n; simp [miuraActionToPaper,miuraActionFromPaper])

theorem miuraActionTopologyEquiv_apply (s : ℕ)
    (a : WeightedCoeff (miuraSpectralActionWeight s) 1) (n : ℤ) :
    (miuraActionTopologyEquiv s a).val n = a.val n := by
  change (miuraActionToPaper s a).val n = a.val n
  exact WeightedCoeff.inclusionCLM_apply _ _ _ a n

def miuraPaperSobolevActionSequence (s : ℕ) (a : ScalarSobolev s) :
    WeightedCoeff (miuraPaperActionWeight s) 1 :=
  miuraActionTopologyEquiv s (miuraSobolevActionSequence s a)

theorem exists_miuraPaperSobolevActionSequence_domain (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧
      {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraPaperSobolevActionSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ, 0 < n → (miuraPaperSobolevActionSequence s b).val n =
        (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraSobolevActionSource s b) := by
  obtain ⟨U,hU,hreal,hA,hcoord⟩ := exists_miuraSobolevActionSequence_domain s
  refine ⟨U,hU,hreal,?_,?_⟩
  · intro b hb
    exact ((miuraActionTopologyEquiv s).analyticAt _).comp (hA b hb)
  · intro b hb n hn
    exact (miuraActionTopologyEquiv_apply s (miuraSobolevActionSequence s b) n).trans (hcoord b hb n hn)

end NLS.MKdV
