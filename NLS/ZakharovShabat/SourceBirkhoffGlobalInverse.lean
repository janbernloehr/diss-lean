import NLS.ZakharovShabat.SourceBirkhoffProposition17_3

/-! # The global analytic Birkhoff inverse for `1 < p ≤ 2`

Propositions 17.1--17.3 give a global homeomorphism whose inverse agrees
locally with each analytic local inverse. Its derivative is the inverse
of the original real Jacobian. The global inverses respect exponent
inclusion, including independently constructed normalized families.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual real Birkhoff map as a global homeomorphism for `1 < p ≤ 2`. -/
def realHomeomorph (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) :
    realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p) :=
  D.real_map_isLocalHomeomorph.toHomeomorphOfBijective ⟨D.proposition17_2,D.proposition17_3 hp2⟩

@[simp] theorem realHomeomorph_apply
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    D.realHomeomorph hp2 φ = sourceRealBirkhoffMap hp hp1 s φ := rfl

/-- Analyticity of the global inverse at every target. -/
theorem realHomeomorph_symm_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) :
    AnalyticOnNhd ℝ (D.realHomeomorph hp2).symm univ := by
  intro y _
  let φ := (D.realHomeomorph hp2).symm y
  have hφ : sourceRealBirkhoffMap hp hp1 s φ = y :=
    (D.realHomeomorph hp2).apply_symm_apply y
  obtain ⟨g,hg,_,_,hr,_⟩ := D.proposition17_1 φ
  rw [hφ] at hg hr
  apply hg.congr
  filter_upwards [hr] with z hz
  apply D.proposition17_2
  exact hz.trans ((D.realHomeomorph hp2).apply_symm_apply z).symm

/-- The exact derivative of the global inverse is the inverse of the
actual real Birkhoff Jacobian at the recovered source. -/
theorem realHomeomorph_symm_hasStrictFDerivAt
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (y : RealCoeff p × RealCoeff p) :
    HasStrictFDerivAt (D.realHomeomorph hp2).symm
      (D.realJacobianEquivAll ((D.realHomeomorph hp2).symm y)).symm.toContinuousLinearMap y := by
  let φ := (D.realHomeomorph hp2).symm y
  have hφ : sourceRealBirkhoffMap hp hp1 s φ = y :=
    (D.realHomeomorph hp2).apply_symm_apply y
  obtain ⟨g,_,_,_,hr,hd⟩ := D.proposition17_1 φ
  rw [hφ] at hr hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hr] with z hz
  apply D.proposition17_2
  exact hz.trans ((D.realHomeomorph hp2).apply_symm_apply z).symm

/-- Inclusion commutes with the global inverse, even when the two
normalized families were constructed independently. -/
theorem realHomeomorph_symm_exponent
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
    {u : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V u)
    (hp2 : p ≤ 2) (hq2 : q ≤ 2) (hpq : p ≤ q) (y : RealCoeff p × RealCoeff p) :
    realTypeSourceExponentInclusion hpq ((D.realHomeomorph hp2).symm y) =
      (E.realHomeomorph hq2).symm
        (((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq)) y) := by
  apply (E.realHomeomorph hq2).injective
  rw [(E.realHomeomorph hq2).apply_symm_apply]
  exact (D.real_map_exponent E hpq ((D.realHomeomorph hp2).symm y)).symm.trans
    (congrArg ((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq))
      ((D.realHomeomorph hp2).apply_symm_apply y))

end SourceBirkhoffMapComplexData

/-- The global bi-real-analytic diffeomorphism of Theorem 14.1(v), with
its normalized family constructed rather than assumed. -/
theorem exists_sourceBirkhoffFamily_globalInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      ∃ e : realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p),
        (∀ φ, e φ = sourceRealBirkhoffMap hp hp1 s φ) ∧
        AnalyticOnNhd ℝ (fun φ => e φ) univ ∧ AnalyticOnNhd ℝ (fun y => e.symm y) univ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.realHomeomorph hp2,fun _ => rfl,D.real_map_analytic,
    D.realHomeomorph_symm_analytic hp2⟩

end NLS.ZakharovShabat
