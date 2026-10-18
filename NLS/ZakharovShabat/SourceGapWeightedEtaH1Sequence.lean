import NLS.ZakharovShabat.SourceAngularBetaH1BallBound
import NLS.ZakharovShabat.SourceGapWeightedEtaAngle
import NLS.ZakharovShabat.SourceAngularRealCharts
import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic

/-! # The actual signed eta sequence in h1

At every real source the signed eta coordinate has norm equal to the
actual gap, including collapsed gaps. On H1 sources this constructs the
actual h1 sequence and bounds its norm by the weighted gap sequence.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- Both actual signed eta coordinates have norm equal to the real gap, including collapsed gaps. -/
theorem norm_gapWeightedEta_eq_gap (φ : realTypeSourceSubmodule p) (n : ℤ)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) :
    ‖sourceGapWeightedEtaCoordinate hp hp1 n s sign φ.val‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap hp hp1 n s φ.val φ.property
      (canonicalPeriodOneBoundaryRoot_mem_omittedDomain hp hp1 .dirichlet φ.val φ.property n) hg sign,
      sourcePeriodicGapDisplacement_apply,hg]
  obtain ⟨O,V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,hδ,E⟩ :=
    D.angular.exists_real_analytic_eta_chart W D.source_open D.source_subset φ.val
      (D.real_subset φ.property) φ.property n hg
  have hη := E.representative_im_eq_zero_of_realType
    D.angular.psi.toSourcePsiIsolatingComplexExtension φ.val hφU φ.property
  rw [E.gapWeightedEtaCoordinate_eq_gap_exp φ.val hφU sign hsign hδ,norm_mul,Complex.norm_exp]
  have he : (sign*I*sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ.val).re = 0 := by
    rcases hsign with rfl | rfl <;> simp [Complex.mul_re,hη]
  rw [he,Real.exp_zero,mul_one,sourcePeriodicGapDisplacement_apply]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The physical weighted gap sequence dominates the actual H1 eta coefficients. -/
theorem gapWeightedEta_H1_majorant (a : realTypeSobolevSourceLocus)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) (n : ℤ) :
    ‖((Weight.sobolev 1 n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s sign (sobolevSourceInclusion a.val)‖ ≤ ‖sourceH1WeightedGapSequence a.val n‖ := by
  have he := D.norm_gapWeightedEta_eq_gap ⟨sobolevSourceInclusion a.val,a.property⟩ n sign hsign
  calc
    _ = (1+|(n:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
        (sobolevSourceInclusion a.val) n‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev 1).positive n).le,he]
      simp only [Weight.sobolev_apply,Real.rpow_one]
    _ ≤ _ := sourceH1WeightedGapSequence_majorant a.val n

/-- The actual eta coordinate as an H1 sequence, without a sequence fallback. -/
def signedEtaH1 (a : realTypeSobolevSourceLocus) (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) :
    WeightedCoeff (Weight.sobolev 1) 2 :=
  ⟨fun n => sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign (sobolevSourceInclusion a.val),by
    change Memℓp (fun n => ((Weight.sobolev 1 n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s sign (sobolevSourceInclusion a.val)) 2
    apply (lp.memℓp (sourceH1WeightedGapSequence a.val)).mono'
    intro n
    exact D.gapWeightedEta_H1_majorant a sign hsign n⟩

@[simp] theorem signedEtaH1_apply (a : realTypeSobolevSourceLocus) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) (n : ℤ) :
    (D.signedEtaH1 a sign hsign).val n =
      sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign (sobolevSourceInclusion a.val) := rfl

/-- The actual eta H1 norm is bounded by the physical weighted gap norm. -/
theorem norm_signedEtaH1_le (a : realTypeSobolevSourceLocus) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) :
    ‖D.signedEtaH1 a sign hsign‖ ≤ ‖sourceH1WeightedGapSequence a.val‖ := by
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 (D.signedEtaH1 a sign hsign)‖ ≤ _
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro n
  exact D.gapWeightedEta_H1_majorant a sign hsign n

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
