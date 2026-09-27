import NLS.ZakharovShabat.SourcePsiDeletedCoordinate

/-!
# Moving one root in the psi numerator

Changing one retained root changes exactly one factor of the literal
product in (2.23). The identity survives the entire-product limit and
gives an affine formula for the numerator along that coordinate line.
This is the first input for the free Jacobian in Lemma 12.5.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Cross-multiplied single-root variation of every sufficiently
large literal deleted product, valid even at the moving free center. -/
theorem jointDeletedSingleSpectralPartialProduct_single_variation
    (n k : ℤ) (hkn : k ≠ n) (N : ℕ) (hN : k.natAbs ≤ N)
    (z t : ℂ) :
    ((Real.pi : ℂ)*k-z) *
      jointDeletedSingleSpectralPartialProduct n N
        (z,(lp.single p k t : Coeff p)) =
      ((Real.pi : ℂ)*k+t-z) *
        jointDeletedSingleSpectralPartialProduct n N (z,(0 : Coeff p)) := by
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n
  have hk : k ∈ s := by
    dsimp [s]
    exact Finset.mem_erase.mpr ⟨hkn, by
      simp only [Finset.mem_Icc]
      constructor <;> omega⟩
  have hother :
      (∏ j ∈ s.erase k,
        singleSpectralFactor (displacedRoots (lp.single p k t : Coeff p)) z j) =
      (∏ j ∈ s.erase k,
        singleSpectralFactor (displacedRoots (0 : Coeff p)) z j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    simp [singleSpectralFactor, displacedRoots, hjk]
  unfold jointDeletedSingleSpectralPartialProduct
  change ((Real.pi : ℂ)*k-z) *
      ((∏ j ∈ s,
        singleSpectralFactor (displacedRoots (lp.single p k t : Coeff p)) z j) /
        singleSpectralDenominator n) =
    ((Real.pi : ℂ)*k+t-z) *
      ((∏ j ∈ s,
        singleSpectralFactor (displacedRoots (0 : Coeff p)) z j) /
        singleSpectralDenominator n)
  rw [← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk,
    hother]
  have hu : singleSpectralFactor
      (displacedRoots (lp.single p k t : Coeff p)) z k =
      ((Real.pi : ℂ)*k+t-z)/singleSpectralDenominator k := by
    simp [singleSpectralFactor, displacedRoots]
  have hzero : singleSpectralFactor (displacedRoots (0 : Coeff p)) z k =
      ((Real.pi : ℂ)*k-z)/singleSpectralDenominator k := by
    simp [singleSpectralFactor, displacedRoots]
  rw [hu,hzero]
  ring

/-- The same cross-multiplied identity for the entire psi numerator. -/
theorem sourcePsiCandidate_single_variation_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (z t : ℂ) :
    ((Real.pi : ℂ)*k-z) *
      sourcePsiCandidate n (z,(lp.single p k t : Coeff p)) =
      ((Real.pi : ℂ)*k+t-z) * sourcePsiFree n z := by
  have hcut : ∀ᶠ N : ℕ in atTop,
      ((Real.pi : ℂ)*k-z) *
        jointDeletedSingleSpectralPartialProduct n N
          (z,(lp.single p k t : Coeff p)) =
      ((Real.pi : ℂ)*k+t-z) *
        jointDeletedSingleSpectralPartialProduct n N
          (z,(0 : Coeff p)) := by
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    exact jointDeletedSingleSpectralPartialProduct_single_variation
      n k hkn N hN z t
  have hleft :=
    (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n
      (z,(lp.single p k t : Coeff p))).const_mul ((Real.pi : ℂ)*k-z)
  have hright :=
    (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n
      (z,(0 : Coeff p))).const_mul ((Real.pi : ℂ)*k+t-z)
  have hlim := tendsto_nhds_unique hleft (hright.congr' (hcut.mono (fun _ h => h.symm)))
  rw [sourcePsiCandidate, ← sourcePsiCandidate_zero hp hp1 n z]
  change ((Real.pi : ℂ)*k-z) *
      (-2*jointDeletedSingleSpectralProduct n
        (z,(lp.single p k t : Coeff p))) =
    ((Real.pi : ℂ)*k+t-z) *
      (-2*jointDeletedSingleSpectralProduct n (z,(0 : Coeff p)))
  linear_combination (-2)*hlim

/-- Away from the selected free center, the psi numerator is affine
in that root-displacement coordinate. -/
theorem sourcePsiCandidate_single_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (z t : ℂ)
    (hzk : z ≠ (Real.pi : ℂ)*k) :
    sourcePsiCandidate n (z,(lp.single p k t : Coeff p)) =
      sourcePsiFree n z +
        t * (sourcePsiFree n z / ((Real.pi : ℂ)*k-z)) := by
  have hden : (Real.pi : ℂ)*k-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzk)
  have hcross := sourcePsiCandidate_single_variation_mul hp hp1 n k hkn z t
  field_simp [hden]
  linear_combination hcross

/-- The exact spectral numerator derivative with respect to one
retained root displacement at the free sequence. -/
theorem hasDerivAt_sourcePsiCandidate_single_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (z : ℂ)
    (hzk : z ≠ (Real.pi : ℂ)*k) :
    HasDerivAt
      (fun t : ℂ => sourcePsiCandidate n
        (z,(lp.single p k t : Coeff p)))
      (sourcePsiFree n z / ((Real.pi : ℂ)*k-z)) 0 := by
  have heq : (fun t : ℂ => sourcePsiCandidate n
      (z,(lp.single p k t : Coeff p))) =
      (fun t : ℂ => sourcePsiFree n z +
        t * (sourcePsiFree n z / ((Real.pi : ℂ)*k-z))) := by
    funext t
    exact sourcePsiCandidate_single_variation hp hp1 n k hkn z t hzk
  rw [heq]
  simpa using (((hasDerivAt_id (0 : ℂ)).mul_const
    (sourcePsiFree n z / ((Real.pi : ℂ)*k-z))).const_add (sourcePsiFree n z))

end NLS.ZakharovShabat
