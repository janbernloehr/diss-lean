import NLS.ZakharovShabat.SourcePsiFreeJacobian
import NLS.SequenceSpaces.Truncation

/-!
# The free psi equation as a Fréchet derivative

For a fixed free-centered contour, the scalar equation is holomorphic
in the omitted-coordinate Banach parameter. Its derivative at the free
sequence is twice coordinate evaluation. This identifies the scalar
rows of the free Jacobian without assuming an `ℓᵖ` bound for the full
sequence-valued equation.
-/

noncomputable section
open Set Metric Complex Filter
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar free-centered equation with the source potential fixed
at zero. -/
def sourcePsiFreeEquation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (r : ℝ) : DeletedCoeff p n → ℂ :=
  fun a => sourcePsiDeletedEquationCoordinate hp hp1 n m a
    (0 : CoeffPair p) ((Real.pi : ℂ)*m) r

/-- A free-centered scalar equation is Fréchet differentiable at the
free displacement sequence. -/
theorem differentiableAt_sourcePsiFreeEquation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    DifferentiableAt ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n) := by
  obtain ⟨V,hVopen,hbase,_,hdiff⟩ :=
    exists_local_sourcePsiEquationCoordinate_differentiableOn
      hp hp1 n m (0 : Coeff p) (0 : CoeffPair p)
      (by simp)
      ((Real.pi : ℂ)*m) r hr.le
      (freeCircle_subset_sourceCanonicalRootDomain hp hp1 m r hr hrπ)
  have hsection : DifferentiableAt ℂ
      (fun b : Coeff p × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m b.1 b.2
          ((Real.pi : ℂ)*m) r) (0,0) :=
    (hdiff (0,0) hbase).differentiableAt (hVopen.mem_nhds hbase)
  have hsub : DifferentiableAt ℂ
      (fun a : DeletedCoeff p n => (a : Coeff p)) 0 :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).differentiableAt
  have hinc : DifferentiableAt ℂ
      (fun a : DeletedCoeff p n => ((a : Coeff p),(0 : CoeffPair p))) 0 :=
    hsub.prodMk (differentiableAt_const (c := (0 : CoeffPair p)))
  change DifferentiableAt ℂ
    (fun a : DeletedCoeff p n => sourcePsiEquationCoordinate hp hp1 n m
      (a : Coeff p) (0 : CoeffPair p) ((Real.pi : ℂ)*m) r) 0
  simpa only [Function.comp_def] using
    hsection.comp (0 : DeletedCoeff p n) hinc

/-- Each retained coordinate direction is an eigenvector of the scalar
free equation derivative, with Kronecker value two. -/
theorem fderiv_sourcePsiFreeEquation_deletedSingle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n) (Coeff.deletedSingleCLM n k hkn 1) =
      if m = k then 2 else 0 := by
  have hF := (differentiableAt_sourcePsiFreeEquation
    hp hp1 n m r hr hrπ).hasFDerivAt
  have hsingle : HasDerivAt (Coeff.deletedSingleCLM (p := p) n k hkn)
      (Coeff.deletedSingleCLM n k hkn 1) 0 :=
    (Coeff.deletedSingleCLM (p := p) n k hkn).hasDerivAt
  have hcomp := hF.comp_hasDerivAt_of_eq (0 : ℂ) hsingle (by simp)
  have hdirect : HasDerivAt
      (fun t : ℂ => sourcePsiFreeEquation hp hp1 n m r
        (Coeff.deletedSingleCLM n k hkn t))
      (if m = k then 2 else 0) 0 :=
    hasDerivAt_sourcePsiDeletedEquationCoordinate_single_zero
      hp hp1 m n k hmn hkn r hr hrπ
  exact hcomp.unique hdirect

/-- The free derivative on an arbitrary retained single-coordinate
sequence, including its complex amplitude. -/
theorem fderiv_sourcePsiFreeEquation_deletedSingle_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) (t : ℂ) :
    fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n) (Coeff.deletedSingleCLM n k hkn t) =
      t * (if m = k then 2 else 0) := by
  let L := fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
    (0 : DeletedCoeff p n)
  have hscaled : Coeff.deletedSingleCLM (p := p) n k hkn t =
      t • Coeff.deletedSingleCLM n k hkn 1 := by
    calc
      _ = Coeff.deletedSingleCLM n k hkn (t • (1 : ℂ)) := by simp
      _ = t • Coeff.deletedSingleCLM n k hkn 1 := map_smul _ _ _
  change L (Coeff.deletedSingleCLM n k hkn t) = _
  rw [hscaled, map_smul,
    fderiv_sourcePsiFreeEquation_deletedSingle hp hp1 n m k hmn hkn r hr hrπ]
  simp [smul_eq_mul]

/-- The derivative composed with coordinate deletion agrees with
twice ambient coordinate evaluation on every elementary sequence. -/
theorem fderiv_sourcePsiFreeEquation_delete_single
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (t : ℂ) :
    (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n))
        (Coeff.deleteCoordinateTo n (lp.single p k t)) =
      2 * (lp.single p k t : Coeff p) m := by
  by_cases hkn : k = n
  · subst k
    rw [Coeff.deleteCoordinateTo_single_same]
    simp [lp.single_apply, hmn]
  · rw [Coeff.deleteCoordinateTo_single_other n k hkn,
      fderiv_sourcePsiFreeEquation_deletedSingle_apply
        hp hp1 n m k hmn hkn r hr hrπ]
    by_cases hmk : m = k
    · subst k
      simp
      ring
    · simp [lp.single_apply, hmk]

/-- Finite truncations extend the elementary residue calculation to
every ambient `ℓᵖ` sequence after deleting the unused coordinate. -/
theorem fderiv_sourcePsiFreeEquation_delete_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (a : Coeff p) :
    (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n)) (Coeff.deleteCoordinateTo n a) =
      2 * a m := by
  let A : Coeff p →L[ℂ] ℂ :=
    (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n)).comp (Coeff.deleteCoordinateTo n)
  let B : Coeff p →L[ℂ] ℂ :=
    (2 : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m
  have hsingle (k : ℤ) (t : ℂ) :
      A (lp.single p k t) = B (lp.single p k t) := by
    change (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n))
        (Coeff.deleteCoordinateTo n (lp.single p k t)) =
      2 * (lp.single p k t : Coeff p) m
    exact fderiv_sourcePsiFreeEquation_delete_single
      hp hp1 n m k hmn r hr hrπ t
  have htrunc (s : Finset ℤ) :
      A (Coeff.truncate s a) = B (Coeff.truncate s a) := by
    simp only [Coeff.truncate, map_sum]
    exact Finset.sum_congr rfl (fun k _ => hsingle k (a k))
  have hlimA : Tendsto (fun s : Finset ℤ => A (Coeff.truncate s a))
      atTop (nhds (A a)) :=
    A.continuous.continuousAt.tendsto.comp (Coeff.tendsto_truncate hp a)
  have hlimB : Tendsto (fun s : Finset ℤ => B (Coeff.truncate s a))
      atTop (nhds (B a)) :=
    B.continuous.continuousAt.tendsto.comp (Coeff.tendsto_truncate hp a)
  have heq : A a = B a :=
    tendsto_nhds_unique hlimA (hlimB.congr' (Eventually.of_forall
      (fun s => (htrunc s).symm)))
  exact heq

/-- The full Fréchet derivative of each scalar free psi equation is
twice evaluation at the corresponding retained coordinate. -/
theorem fderiv_sourcePsiFreeEquation_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (a : DeletedCoeff p n) :
    (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n)) a = 2 * (a : Coeff p) m := by
  have hfixed : Coeff.deleteCoordinateTo n (a : Coeff p) = a := by
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (a : Coeff p)).2 a.property
  simpa only [hfixed] using
    fderiv_sourcePsiFreeEquation_delete_apply
      hp hp1 n m hmn r hr hrπ (a : Coeff p)

/-- The scalar free Jacobian row is the bounded coordinate functional
`2 · eval_m` restricted to the deleted-coordinate space. -/
theorem fderiv_sourcePsiFreeEquation_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n) =
      (2 : ℂ) • ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL) := by
  ext a
  exact fderiv_sourcePsiFreeEquation_apply
    hp hp1 n m hmn r hr hrπ a

end NLS.ZakharovShabat
