import NLS.ZakharovShabat.SourcePsiSingleVariation

/-!
# Varying one retained psi root at arbitrary displacement data

The finite deleted product changes in exactly one factor when one
retained root moves. Passing to the entire-product limit gives a
cross-multiplied identity valid even when roots collide. Away from the
original root, it gives an exact affine variation and derivative of
the psi numerator. This is an input to the nonfree matrix elements in
Lemma 12.5.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Moving one retained root changes one factor of every sufficiently
large literal deleted product, at any base displacement sequence. -/
theorem jointDeletedSingleSpectralPartialProduct_variation_mul
    (n k : ℤ) (hkn : k ≠ n) (N : ℕ) (hN : k.natAbs ≤ N)
    (a : Coeff p) (z t : ℂ) :
    (displacedRoots a k-z) *
      jointDeletedSingleSpectralPartialProduct n N
        (z,a+lp.single p k t) =
    (displacedRoots a k+t-z) *
        jointDeletedSingleSpectralPartialProduct n N (z,a) := by
  let b : Coeff p := a+lp.single p k t
  change (displacedRoots a k-z) *
      jointDeletedSingleSpectralPartialProduct n N (z,b) =
    (displacedRoots a k+t-z) *
      jointDeletedSingleSpectralPartialProduct n N (z,a)
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n
  have hk : k ∈ s := by
    dsimp [s]
    exact Finset.mem_erase.mpr ⟨hkn, by
      simp only [Finset.mem_Icc]
      constructor <;> omega⟩
  have hroot_other (j : ℤ) (hjk : j ≠ k) :
      displacedRoots b j = displacedRoots a j := by
    change (Real.pi : ℂ)*j + (a+lp.single p k t : Coeff p) j =
      (Real.pi : ℂ)*j + a j
    simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply_ne _ _ _ hjk,
      add_zero]
  have hroot_same :
      displacedRoots b k = displacedRoots a k+t := by
    change (Real.pi : ℂ)*k + (a+lp.single p k t : Coeff p) k =
      ((Real.pi : ℂ)*k+a k)+t
    simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply_self]
    ring
  have hother :
      (∏ j ∈ s.erase k,
        singleSpectralFactor (displacedRoots b) z j) =
      (∏ j ∈ s.erase k,
        singleSpectralFactor (displacedRoots a) z j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    unfold singleSpectralFactor
    rw [hroot_other j hjk]
  unfold jointDeletedSingleSpectralPartialProduct
  change (displacedRoots a k-z) *
      ((∏ j ∈ s,
        singleSpectralFactor (displacedRoots b) z j) /
        singleSpectralDenominator n) =
    (displacedRoots a k+t-z) *
      ((∏ j ∈ s,
        singleSpectralFactor (displacedRoots a) z j) /
        singleSpectralDenominator n)
  rw [← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk,
    hother]
  have hu : singleSpectralFactor
      (displacedRoots b) z k =
      (displacedRoots a k+t-z)/singleSpectralDenominator k := by
    rw [singleSpectralFactor, hroot_same]
  have hbase : singleSpectralFactor (displacedRoots a) z k =
      (displacedRoots a k-z)/singleSpectralDenominator k := by
    rfl
  rw [hu,hbase]
  ring

/-- The cross-multiplied variation identity for the entire psi
numerator, valid at arbitrary base displacements and all spectral
parameters. -/
theorem sourcePsiCandidate_variation_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a : Coeff p) (z t : ℂ) :
    (displacedRoots a k-z) *
      sourcePsiCandidate n (z,a+lp.single p k t) =
      (displacedRoots a k+t-z) * sourcePsiCandidate n (z,a) := by
  let b : Coeff p := a+lp.single p k t
  change (displacedRoots a k-z) * sourcePsiCandidate n (z,b) =
    (displacedRoots a k+t-z) * sourcePsiCandidate n (z,a)
  have hcut : ∀ᶠ N : ℕ in atTop,
      (displacedRoots a k-z) *
        jointDeletedSingleSpectralPartialProduct n N
          (z,b) =
      (displacedRoots a k+t-z) *
        jointDeletedSingleSpectralPartialProduct n N (z,a) := by
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    exact jointDeletedSingleSpectralPartialProduct_variation_mul
      n k hkn N hN a z t
  have hleft :=
    (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n
      (z,b)).const_mul (displacedRoots a k-z)
  have hright :=
    (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n
      (z,a)).const_mul (displacedRoots a k+t-z)
  have hlim := tendsto_nhds_unique hleft
    (hright.congr' (hcut.mono (fun _ h => h.symm)))
  change (displacedRoots a k-z) *
      (-2*jointDeletedSingleSpectralProduct n (z,b)) =
    (displacedRoots a k+t-z) *
      (-2*jointDeletedSingleSpectralProduct n (z,a))
  linear_combination (-2)*hlim

/-- Away from the original retained root, the entire numerator is
affine along that root's coordinate line. -/
theorem sourcePsiCandidate_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a : Coeff p) (z t : ℂ)
    (hzk : z ≠ displacedRoots a k) :
    sourcePsiCandidate n (z,a+lp.single p k t) =
      sourcePsiCandidate n (z,a) +
        t * (sourcePsiCandidate n (z,a) / (displacedRoots a k-z)) := by
  have hden : displacedRoots a k-z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hzk)
  have hcross := sourcePsiCandidate_variation_mul
    hp hp1 n k hkn a z t
  field_simp [hden]
  linear_combination hcross

/-- The exact numerator derivative along any retained root coordinate
at an arbitrary base displacement sequence. -/
theorem hasDerivAt_sourcePsiCandidate_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a : Coeff p) (z : ℂ)
    (hzk : z ≠ displacedRoots a k) :
    HasDerivAt
      (fun t : ℂ => sourcePsiCandidate n (z,a+lp.single p k t))
      (sourcePsiCandidate n (z,a) / (displacedRoots a k-z)) 0 := by
  have heq : (fun t : ℂ => sourcePsiCandidate n (z,a+lp.single p k t)) =
      (fun t : ℂ => sourcePsiCandidate n (z,a) +
        t * (sourcePsiCandidate n (z,a) / (displacedRoots a k-z))) := by
    funext t
    exact sourcePsiCandidate_variation hp hp1 n k hkn a z t hzk
  rw [heq]
  simpa using (((hasDerivAt_id (0 : ℂ)).mul_const
    (sourcePsiCandidate n (z,a) / (displacedRoots a k-z))).const_add
      (sourcePsiCandidate n (z,a)))

end NLS.ZakharovShabat
