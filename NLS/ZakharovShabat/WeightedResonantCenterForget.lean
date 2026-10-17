import NLS.ZakharovShabat.WeightedResonantDiagonalCenter

/-! # Diagonal centers do not depend on the Fourier weight

The complementary inverse agrees with its unit-weight realization on
the common contraction domain. Uniqueness of the diagonal equation
then identifies the moving centers, and hence both closing equations,
at every sufficiently distant frequency.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem common_open_neighborhood
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (J : E → F) (hJ : Continuous J) (a : E) (U R : Set E) (V : Set F)
    (hU : IsOpen U) (hR : IsOpen R) (hV : IsOpen V)
    (haU : a ∈ U) (haR : a ∈ R) (haV : J a ∈ V) :
    ∃ Z : Set E, IsOpen Z ∧ a ∈ Z ∧ ∀ x ∈ Z, x ∈ U ∧ x ∈ R ∧ J x ∈ V := by
  exact ⟨(U ∩ R) ∩ (J ⁻¹' V),(hU.inter hR).inter (hV.preimage hJ),
    ⟨⟨haU,haR⟩,haV⟩,fun _ hx => ⟨hx.1.1,hx.1.2,hx.2⟩⟩

private theorem center_forget_of_spec
    (hp : p ≠ ⊤) (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (hz : weightedResonantDiagonalCenter hp w ψ n ∈ resonantStrip n)
    (hfix : weightedResonantDiagonalCenter hp w ψ n = (Real.pi : ℂ)*n+
      weightedResonantAExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n))
    (hunique : ∀ z ∈ resonantStrip n,
      z = (Real.pi : ℂ)*n+weightedResonantAExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n z →
        z = weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n)
    (hw : ‖weightedPotentialSquareInShift hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) hz‖ < 1)
    (hu : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight ψ) n
      (weightedResonantDiagonalCenter hp w ψ n) hz‖ < 1) :
    weightedResonantDiagonalCenter hp w ψ n =
        weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n ∧
      weightedResonantBPlusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) =
        weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n) ∧
      weightedResonantBMinusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) =
        weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n) := by
  let ζ := weightedResonantDiagonalCenter hp w ψ n
  have hentry (i j : Fin 2) := weightedCorrectionEntryExtension_forget hp w ψ n ζ hz hw hu i j
  have ha : weightedResonantAExtension hp w ψ n ζ =
      weightedResonantAExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n ζ := hentry 0 0
  have hcenter : ζ = weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n :=
    hunique ζ hz (ha ▸ hfix)
  refine ⟨hcenter,?_,?_⟩
  · exact (hentry 1 0).trans (congrArg
      (weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n) hcenter)
  · exact (hentry 0 1).trans (congrArg
      (weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n) hcenter)

/-- On one common weighted neighborhood, all distant centers and closing
equations agree with their unit-weight realizations. -/
theorem exists_uniform_weightedResonantCenter_forget
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
      weightedResonantDiagonalCenter hp w ψ n =
        weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n ∧
      weightedResonantBPlusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) =
        weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n) ∧
      weightedResonantBMinusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) =
        weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight ψ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight ψ) n) := by
  obtain ⟨Nw,hNw,Uw,how,_,hφw,_,hw⟩ :=
    exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  obtain ⟨Nu,_,Uu,hou,_,hφu,_,hu⟩ :=
    exists_uniform_weightedResonantDiagonalCenters hp hp1 SpectralWeight.one (w.forgetPairWeight φ)
  obtain ⟨Nc,_,Uc,hoc,_,hφc,_,_,hc⟩ := exists_uniform_complementarySquare_half hp w φ
  obtain ⟨U,ho,hφ,hsub⟩ := common_open_neighborhood w.forgetPairWeight
    w.forgetPairWeight.continuous φ Uw Uc Uu how hoc hou hφw hφc hφu
  refine ⟨max Nw (max Nu Nc),hNw.trans (le_max_left _ _),U,ho,hφ,?_⟩
  intro ψ hψ n hn
  obtain ⟨hψw,hψc,hψu⟩ := hsub ψ hψ
  have hwdata := (hw ψ hψw n (by omega)).1
  have hudata := (hu (w.forgetPairWeight ψ) hψu n (by omega)).1
  let ζ := weightedResonantDiagonalCenter hp w ψ n
  have hz : ζ ∈ resonantStrip n := refinedResonantDisk_subset_strip n hwdata.1
  obtain ⟨hwsmall,husmall⟩ := hc ψ hψc n (by omega) ζ hz
  rw [← norm_weightedPotentialSquareInShift_one hp] at husmall
  exact center_forget_of_spec hp w ψ n hz hwdata.2.2.1 hudata.2.2.2
    (hwsmall.trans_lt (by norm_num)) (husmall.trans_lt (by norm_num))

/-- At a fixed source, all sufficiently distant diagonal centers and
both off-diagonal values at those centers agree after forgetting the
weight. The assertion includes the actual named centers. -/
theorem exists_weightedResonantCenter_forget
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      weightedResonantDiagonalCenter hp w φ n =
        weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n ∧
      weightedResonantBPlusExtension hp w φ n (weightedResonantDiagonalCenter hp w φ n) =
        weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n) ∧
      weightedResonantBMinusExtension hp w φ n (weightedResonantDiagonalCenter hp w φ n) =
        weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n) := by
  obtain ⟨N,hN,U,_,hφ,h⟩ := exists_uniform_weightedResonantCenter_forget hp hp1 w φ
  exact ⟨N,hN,h φ hφ⟩

end NLS.ZakharovShabat
