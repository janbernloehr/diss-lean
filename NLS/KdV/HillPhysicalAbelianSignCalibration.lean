import NLS.ComplexAnalysis.RealAnalyticGermSign
import NLS.KdV.HillRealSourceSubmodule
import NLS.KdV.HillAbelianCoordinateAnalytic
import NLS.KdV.HillArbitraryRoughAbelianSigns
import NLS.SequenceSpaces.ConstantSignPacketTransport

/-! # Canonical physical signs on arbitrary rough balls

Real analyticity of the ORIGINAL Abelian coordinate fixes one sign on
an entire physical rough-ball preimage. The source is the actual real L2
Banach space, with arbitrary means and no bound on its L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro n; simp

/-- The literal original physical Abelian coordinate is real analytic
at EVERY original real L2 source, including all closed gaps. -/
theorem analyticOnNhd_hillPhysicalAbelianCoordinate (n : ℕ+) :
    AnalyticOnNhd ℝ (fun p : hillRealSourceSubmodule =>
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos) univ := by
  intro p _
  obtain ⟨Z,hZ,_hZ0,_hDZ,hmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension p.val p.property.1 p.property.2
      zero_parity zero_real n n.pos
  let L : hillRealSourceSubmodule →L[ℝ] Coeff 2 :=
    (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hZr : AnalyticAt ℝ Z (L p) := hZ.restrictScalars (𝕜 := ℝ)
  have hA : AnalyticAt ℝ (fun q => Z (L q)) p :=
    hZr.comp (L.analyticAt p)
  have hQ : Continuous (fun q : hillRealSourceSubmodule =>
      (⟨q.val,q.property⟩ : RealPeriodOneHillPotential)) :=
    continuous_subtype_val.subtype_mk _
  exact hA.congr (hQ.continuousAt.tendsto.eventually hmatch)

/-- Continuity removes the actual own-sheet restriction on ANY open
physical source domain. -/
theorem eqOn_physical_of_sheet_regular_eq
    {Y : Type*} [NormedAddCommGroup Y]
    (U : Set RealPeriodOneHillPotential) (hU : IsOpen U) (n : ℕ+)
    (f g : RealPeriodOneHillPotential → Y) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ p ∈ U, hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
      (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) ≠ 0 → f p = g p) :
    EqOn f g U := by
  let S := {p : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
    (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) ≠ 0}
  have hS : Dense S := dense_hillDirichletSheetRoot_ne_zero n n.pos
  have hEq : EqOn f g (U ∩ S) := fun p hp => he p hp.1 hp.2
  exact hEq.of_subset_closure hf hg inter_subset_left (fun p hp => hU.inter_closure ⟨hp,hS p⟩)

/-- ONE infinite sign selection recovers the exact ORIGINAL physical
coordinates throughout the whole rough ball. The rough center may be
non-L2; all physical means and L2 norms are allowed. -/
theorem exists_physical_signChange_rough_packet
    (q0 : PeriodOneHminusOne) (r : ℝ) (G : PeriodOneHminusOne → Coeff 2)
    (hGa : AnalyticOnNhd ℂ G (ball q0 r))
    (hGzero : ∀ q ∈ ball q0 r, ∀ j : ℤ, j ≤ 0 → G q j = 0)
    (hGphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val ∈ ball q0 r → ∀ n : ℕ+,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) ≠ 0 →
      (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2 =
        (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ)) :
    ∃ e : ℤ → Bool,
      (∀ q ∈ ball q0 r, ∀ j : ℤ, j ≤ 0 → Coeff.signChange e (G q) j = 0) ∧
      ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val ∈ ball q0 r →
        ∀ n : ℕ+, Coeff.signChange e (G (hillPhysicalHminusEmbedding p).val) (n : ℤ) =
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
            (Real.sqrt (1+(n : ℝ)) : ℂ) := by
  classical
  let L : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  let U := L ⁻¹' ball q0 r
  have hU : IsOpen U := isOpen_ball.preimage L.continuous
  have hconv : Convex ℝ U := (convex_ball q0 r).linear_preimage L.toLinearMap
  have hchoice (j : ℤ) : ∃ b : Bool, ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val ∈ ball q0 r → ∀ n : ℕ+, (n : ℤ) = j →
      (if b then -G (hillPhysicalHminusEmbedding p).val j else G (hillPhysicalHminusEmbedding p).val j) =
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ) := by
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ) = j := by change (j.toNat : ℤ) = j; omega
      let f : hillRealSourceSubmodule → ℂ := fun p => G (L p) (n : ℤ)
      let g : hillRealSourceSubmodule → ℂ := fun p =>
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ)
      have hf : AnalyticOnNhd ℝ f U := fun p hp =>
        ((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp
          (hGa (L p) hp)).restrictScalars (𝕜 := ℝ)).comp (L.analyticAt p)
      have hg : AnalyticOnNhd ℝ g U := fun p _ =>
        (analyticOnNhd_hillPhysicalAbelianCoordinate n p (mem_univ _)).div_const
      have hsqrt : (Real.sqrt (1+(n : ℝ)) : ℂ)^2 = (1+(n : ℕ) : ℂ) := by
        rw [←ofReal_pow,Real.sq_sqrt (by positivity),ofReal_add,ofReal_one,ofReal_natCast]
      have hsq : ∀ p ∈ U, (f p)^2 = (g p)^2 := by
        let V := (fun p : RealPeriodOneHillPotential => (hillPhysicalHminusEmbedding p).val) ⁻¹' ball q0 r
        have hV : IsOpen V := isOpen_ball.preimage
          (continuous_subtype_val.comp continuous_hillPhysicalHminusEmbedding)
        have hF : ContinuousOn (fun p : RealPeriodOneHillPotential =>
            (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2) V :=
          (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).continuous.comp_continuousOn
            hGa.continuousOn).comp
              (continuous_subtype_val.comp continuous_hillPhysicalHminusEmbedding).continuousOn
              (fun _ h => h)).pow 2
        have hC : ContinuousOn (fun p : RealPeriodOneHillPotential =>
            (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
              (Real.sqrt (1+(n : ℝ)) : ℂ))^2) V :=
          ((continuous_hillDirichletAbelianCoordinate zero_parity zero_real n n.pos).div_const _).pow 2 |>.continuousOn
        have H := eqOn_physical_of_sheet_regular_eq V hV n _ _ hF hC (by
          intro p hp hw
          rw [hGphys p hp n hw,div_pow,hsqrt])
        intro p hp
        exact H (show (⟨p.val,p.property⟩ : RealPeriodOneHillPotential) ∈ V from hp)
      by_cases hne : U.Nonempty
      · obtain ⟨a,ha⟩ := hne
        have H := real_analytic_eqOn_or_neg_of_sq_eq U hU hconv.isPreconnected a ha f g hf hg hsq
        rcases H with he | he
        · refine ⟨false,?_⟩
          intro p hp m hm
          have hmn : m = n := by
            have hcast : (m : ℤ) = (n : ℤ) := hm.trans hn.symm
            apply Subtype.ext
            change (m : ℕ) = (n : ℕ)
            omega
          subst m
          have hh := he (show (⟨p.val,p.property⟩ : hillRealSourceSubmodule) ∈ U from hp)
          change G (hillPhysicalHminusEmbedding p).val (n : ℤ) =
            hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
              (Real.sqrt (1+(n : ℝ)) : ℂ) at hh
          simpa only [hn,Bool.false_eq_true,↓reduceIte] using hh
        · refine ⟨true,?_⟩
          intro p hp m hm
          have hmn : m = n := by
            have hcast : (m : ℤ) = (n : ℤ) := hm.trans hn.symm
            apply Subtype.ext
            change (m : ℕ) = (n : ℕ)
            omega
          subst m
          have hh := he (show (⟨p.val,p.property⟩ : hillRealSourceSubmodule) ∈ U from hp)
          change G (hillPhysicalHminusEmbedding p).val (n : ℤ) =
            -(hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
              (Real.sqrt (1+(n : ℝ)) : ℂ)) at hh
          simpa only [hn,↓reduceIte,neg_neg] using congrArg Neg.neg hh
      · exact ⟨false,fun p hp _ _ => (hne ⟨⟨p.val,p.property⟩,hp⟩).elim⟩
    · refine ⟨false,?_⟩
      intro p hp n hn
      have hnp : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.pos
      omega
  choose e he using hchoice
  refine ⟨e,?_,?_⟩
  · intro q hq j hj
    rw [Coeff.signChange_apply,hGzero q hq j hj]
    simp only [neg_zero,ite_self]
  · intro p hp n
    rw [Coeff.signChange_apply]
    exact he (n : ℤ) p hp n rfl

end NLS.KdV
