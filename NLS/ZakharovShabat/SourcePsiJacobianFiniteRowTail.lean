import NLS.ZakharovShabat.SourcePsiGlobalHeadKernelBound
import NLS.ZakharovShabat.SourcePsiJacobianKernelBound
import NLS.ZakharovShabat.SourcePsiCommonJacobianCharts
import NLS.SequenceSpaces.FiniteOutputReciprocalTail

/-!
# Input tails of finitely many psi Jacobian rows

Compact bounds on fixed selected circles control the standard-root
kernel and quotient. Distant free centers control the omitted root,
and distant input roots give reciprocal lattice decay. Hölder then
makes all high input frequencies small uniformly on finite output sets.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat

/-- Fixed finitely many valid selected contours share one reciprocal
scalar entry bound on all distant input columns, eventually in the
deleted index. The contours need not be free-centered. -/
theorem exists_sourcePsi_escaping_finiteRow_scalarReciprocalBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m)
    (hdom : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 φ m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 φ) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m ∈ s, ∀ k : ℤ, K ≤ k.natAbs → ∀ hkn : k ≠ n, m ≠ k →
          ‖deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a + Coeff.deletedSingleCLM n k hkn t)
                φ (c m) (R m)) 0‖ ≤ C/‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨U,hUopen,hbase,M,hM,hquot⟩ :=
    exists_local_sourcePsiQuotient_uniformFiniteSelectedDiscBound hp hp1 φ hφ s c R hdom a
  obtain ⟨V,_,hφV,Mker,hMker,hker⟩ :=
    exists_local_sourceStandardRoot_inv_uniformFiniteCircleBound hp hp1 φ hφ s c R hcircle
  obtain ⟨L,hL⟩ := exists_uniform_shifted_disc_lattice_cutoff s c R (fun m _ => hR m)
  obtain ⟨Ksmall,hsmall⟩ := Coeff.exists_cutoff_norm_apply_lt hp a
    (by positivity : (0 : ℝ) < Real.pi/4)
  let H : ℕ := ∑ m ∈ s, m.natAbs
  let N : ℕ := H+L+1
  let K : ℕ := max Ksmall N
  let D : ℝ := ∑ m ∈ s, (‖((Real.pi : ℂ)*m)-c m‖+R m)
  let S : ℝ := ∑ m ∈ s, R m
  let A : ℝ := (‖a‖+D)*Mker
  let B : ℝ := (2/Real.pi)*(1+M)
  let δ : ℝ := Real.pi/4
  let C : ℝ := 2*Real.pi*S*(A*B)/δ
  have hD : 0 ≤ D := Finset.sum_nonneg (fun m _ => add_nonneg (norm_nonneg _) (hR m))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun m _ => hR m)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hparam : Tendsto (fun n : ℤ => (Coeff.deleteCoordinate n a,φ))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (a,φ)) := by
    simpa only [nhds_prod_eq] using
      (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).prodMk (tendsto_const_nhds (x := φ))
  have hnear := hparam.eventually (hUopen.mem_nhds hbase)
  have hfar : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop, N ≤ n.natAbs :=
    eventually_comap.mpr (eventually_atTop.mpr ⟨N,fun j hj n hn => hn ▸ hj⟩)
  refine ⟨K,C,hC,?_⟩
  filter_upwards [hnear,hfar] with n hn hnfar
  intro m hm k hk hkn hmk
  let aₙ : DeletedCoeff p n := Coeff.deleteCoordinateTo n a
  have hmH : m.natAbs ≤ H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
  have hdistN : L ≤ (n-m).natAbs := by
    have htri : n.natAbs ≤ (n-m).natAbs+m.natAbs := by
      simpa only [sub_add_cancel] using Int.natAbs_add_le (n-m) m
    dsimp [N] at hnfar
    omega
  have hdistK : L ≤ (k-m).natAbs := by
    have htri : k.natAbs ≤ (k-m).natAbs+m.natAbs := by
      simpa only [sub_add_cancel] using Int.natAbs_add_le (k-m) m
    dsimp [K,N] at hk
    omega
  have hmn : m ≠ n := by dsimp [N] at hnfar; omega
  have hnsep := hL m hm n hdistN
  have hksep := hL m hm k hdistK
  have hnroot : displacedRoots (aₙ : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [aₙ,Coeff.deleteCoordinateTo,displacedRoots,Coeff.deleteCoordinate_apply_same]
  have hak : ‖(aₙ : Coeff p) k‖ ≤ Real.pi/4 := by
    have hkSmall : Ksmall ≤ k.natAbs := by dsimp [K] at hk; omega
    simpa [aₙ,Coeff.deleteCoordinateTo,Coeff.deleteCoordinate_apply_other n k hkn]
      using (hsmall k hkSmall).le
  have hindex : 1 ≤ ‖((m-k : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmk)
  have habsSwap : |((k-m : ℤ) : ℝ)| = ‖((m-k : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have heq : ((k-m : ℤ) : ℝ) = -((m-k : ℤ) : ℝ) := by push_cast; ring
    rw [heq,abs_neg]
  have hsep (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      δ*‖((m-k : ℤ) : ℂ)‖ ≤ ‖displacedRoots (aₙ : Coeff p) k-z‖ := by
    have hfree := shifted_disc_free_lattice_distance_lower k m (c m) (R m) hksep
      z (sphere_subset_closedBall hz)
    rw [habsSwap] at hfree
    have heq : (Real.pi : ℂ)*k-z =
        (displacedRoots (aₙ : Coeff p) k-z)-(aₙ : Coeff p) k := by
      simp only [displacedRoots]
      ring
    have htri : ‖(Real.pi : ℂ)*k-z‖ ≤
        ‖displacedRoots (aₙ : Coeff p) k-z‖+‖(aₙ : Coeff p) k‖ := by
      rw [heq]
      exact norm_sub_le _ _
    dsimp [δ]
    nlinarith [Real.pi_pos]
  have havoidk (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      z ≠ displacedRoots (aₙ : Coeff p) k := by
    have hpos : 0 < ‖displacedRoots (aₙ : Coeff p) k-z‖ := by
      nlinarith [hsep z hz]
    exact Ne.symm (sub_ne_zero.mp (norm_pos_iff.mp hpos))
  have havoidn (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      z ≠ displacedRoots (aₙ : Coeff p) n := by
    have hfree := shifted_disc_free_lattice_distance_lower n m (c m) (R m) hnsep
      z (sphere_subset_closedBall hz)
    have hidx : 1 ≤ |((n-m : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn.symm)
    have hpos : 0 < ‖(Real.pi : ℂ)*n-z‖ := by nlinarith [Real.pi_pos]
    rw [hnroot]
    exact Ne.symm (sub_ne_zero.mp (norm_pos_iff.mp hpos))
  have hkernel (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      ‖(displacedRoots (aₙ : Coeff p) m-z)/sourceStandardRoot hp hp1 φ m z‖ ≤ A := by
    have hacoord : ‖(aₙ : Coeff p) m‖ ≤ ‖a‖ := by
      simpa [aₙ,Coeff.deleteCoordinateTo,Coeff.deleteCoordinate_apply_other n m hmn]
        using lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a m
    have hDm : ‖((Real.pi : ℂ)*m)-c m‖+R m ≤ D :=
      Finset.single_le_sum (f := fun j => ‖((Real.pi : ℂ)*j)-c j‖+R j)
        (fun j _ => add_nonneg (norm_nonneg _) (hR j)) hm
    have hzR : ‖c m-z‖ = R m := by
      simpa only [dist_eq_norm,norm_sub_rev] using mem_sphere.mp hz
    have hnum : ‖displacedRoots (aₙ : Coeff p) m-z‖ ≤ ‖a‖+D := by
      have heq : displacedRoots (aₙ : Coeff p) m-z =
          (aₙ : Coeff p) m+(((Real.pi : ℂ)*m)-c m)+(c m-z) := by
        simp only [displacedRoots]
        ring
      rw [heq]
      have htri : ‖(aₙ : Coeff p) m+(((Real.pi : ℂ)*m)-c m)+(c m-z)‖ ≤
          ‖(aₙ : Coeff p) m‖+‖((Real.pi : ℂ)*m)-c m‖+‖c m-z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      rw [hzR] at htri
      linarith
    rw [div_eq_mul_inv,norm_mul]
    exact mul_le_mul hnum (hker φ hφV m hm z hz) (norm_nonneg _) (by positivity)
  have hregular (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      ‖((n-m : ℤ) : ℂ)*sourcePsiGapRegularFactor hp hp1 n m (aₙ : Coeff p) φ z‖ ≤ B := by
    let major : Coeff p := lp.single p m (M : ℂ)
    have hquotMajor : ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((aₙ : Coeff p),φ))-1‖ ≤ ‖major m‖ := by
      simpa [major,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
        using hquot ((aₙ : Coeff p),φ) hn m hm z (sphere_subset_closedBall hz)
    simpa [B,major,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] using
      norm_deletedPsi_gapRegularFactor_weighted_le_on_shifted_disc hp hp1 n m hmn.symm
        aₙ φ major (c m) (R m) hnsep z (sphere_subset_closedBall hz) hquotMajor
  have hnum (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
      ‖((n-m : ℤ) : ℂ)*sourcePsiContourIntegrandJoint hp hp1 n
        (z,((aₙ : Coeff p),φ))‖ ≤ A*B := by
    rw [sourcePsiContourIntegrandJoint_eq_gap_factor hp hp1 n m (aₙ : Coeff p) φ z
      (hcircle m hz) (havoidn z hz)]
    have heq : ((n-m : ℤ) : ℂ) *
        (((displacedRoots (aₙ : Coeff p) m-z)/sourceStandardRoot hp hp1 φ m z) *
          sourcePsiGapRegularFactor hp hp1 n m (aₙ : Coeff p) φ z) =
        ((displacedRoots (aₙ : Coeff p) m-z)/sourceStandardRoot hp hp1 φ m z) *
          (((n-m : ℤ) : ℂ)*sourcePsiGapRegularFactor hp hp1 n m (aₙ : Coeff p) φ z) := by ring
    rw [heq,norm_mul]
    exact mul_le_mul (hkernel z hz) (hregular z hz) (norm_nonneg _) hA
  rw [(hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation hp hp1 n m k hkn
    aₙ φ hφ (c m) (R m) (hR m) (hcircle m) havoidk).deriv]
  have hbound := norm_sourcePsiRootVariation_slope_le_of_circle_bounds
    hp hp1 n m k hmk (aₙ : Coeff p) φ (c m) (R m) (hR m)
      (A*B) δ (by positivity) hδ hnum hsep
  have hSm : R m ≤ S := Finset.single_le_sum (fun j _ => hR j) hm
  calc
    _ ≤ 2*Real.pi*(R m)*((A*B)/(δ*‖((m-k : ℤ) : ℂ)‖)) := hbound
    _ ≤ 2*Real.pi*S*((A*B)/(δ*‖((m-k : ℤ) : ℂ)‖)) := by gcongr
    _ = C/‖((m-k : ℤ) : ℂ)‖ := by dsimp [C]; field_simp

/-- The scalar finite-row reciprocal bound holds for the actual
common-space Jacobians, including their zero deleted row and column. -/
theorem sourcePsiFullRootJacobian_finiteRows_reciprocalBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m)
    (hdom : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 φ m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 φ)
    (hmatrix : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
          deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m ∈ s, ∀ k : ℤ, K ≤ k.natAbs → k ≠ m →
          ‖(sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m‖ ≤
              C/|((k-m : ℤ) : ℝ)| := by
  obtain ⟨K,C,hC,hscalar⟩ := exists_sourcePsi_escaping_finiteRow_scalarReciprocalBound
    hp hp1 a φ hφ s c R hR hdom hcircle
  refine ⟨K,C,hC,?_⟩
  filter_upwards [hscalar,hmatrix] with n hn hmat
  intro m hm k hk hkm
  by_cases hmn : m = n
  · subst m
    rw [sourcePsiFullRootJacobian_entry_deleted_row hp hp1 n k hkm]
    simpa only [norm_zero] using div_nonneg hC (abs_nonneg (((k-n : ℤ) : ℝ)))
  by_cases hkn : k = n
  · subst k
    rw [sourcePsiFullRootJacobian_entry_deleted_column hp hp1 n m hmn]
    simpa only [norm_zero] using div_nonneg hC (abs_nonneg (((n-m : ℤ) : ℝ)))
  rw [hmat m k hmn hkn]
  have hbound := hn m hm k hk hkn hkm.symm
  rw [Complex.norm_intCast,Int.cast_sub,abs_sub_comm,← Int.cast_sub] at hbound
  exact hbound

/-- Every fixed finite output projection of the common psi Jacobians
has a uniformly small high-input block, eventually in the deleted
index. This is the remaining mixed-tail direction in Lemma 12.10. -/
theorem sourcePsiFullRootJacobian_finiteOutput_uniformInputTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m)
    (hdom : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 φ m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 φ)
    (hmatrix : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
          deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) :
    ∀ s : Finset ℤ, ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℤ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(Coeff.truncateCLM s).comp
          ((sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ).comp
            (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε := by
  intro s ε hε
  obtain ⟨K,C,hC,hentries⟩ := sourcePsiFullRootJacobian_finiteRows_reciprocalBound
    hp hp1 a φ hφ s c R hR hdom hcircle hmatrix
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  obtain ⟨t,ht⟩ := Coeff.exists_uniform_finiteOutput_inputTail_cutoff_of_reciprocalEntries
    p.conjExponent hp hq s K C hC ε hε
  refine ⟨t,?_⟩
  filter_upwards [hentries] with n hn
  exact ht _ hn

end NLS.ZakharovShabat
