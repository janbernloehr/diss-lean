import NLS.SequenceSpaces.TailSquareDescentHeadAnalytic
import NLS.ComplexAnalysis.AnalyticSquareDescent

/-! # Scalar analyticity in squared tail coordinates

Each scalar continuous linear observation of a descended map is analytic
in any one squared tail coordinate, including at zero. This is separate
coordinate analyticity; joint Banach-space analyticity remains to be proved.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Insert a scalar in one coordinate of the first (`false`) or second
(`true`) coefficient sequence. -/
def pairSingleCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (second : Bool) (k : ℤ) :
    ℂ →L[ℂ] (Coeff p × Coeff p) :=
  if second then (0 : ℂ →L[ℂ] Coeff p).prod (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k)
  else (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k).prod (0 : ℂ →L[ℂ] Coeff p)

variable [p.HolderTriple p q]

/-- Changing one tail root changes just its squared coordinate. -/
theorem pairMixedSquare_add_pairSingle (S : Finset ℤ) (z : Coeff p × Coeff p)
    (second : Bool) (k : ℤ) (hk : k ∉ S) (w : ℂ) :
    let a := if second then z.2 k else z.1 k
    pairMixedSquare (q := q) S (z+pairSingleCLM p second k (w-a)) =
      pairMixedSquare S z+pairSingleCLM q second k (w^2-a^2) := by
  classical
  cases second <;> apply Prod.ext <;> ext n <;>
    by_cases hn : n = k <;> by_cases hs : n ∈ S <;>
    simp_all [pairMixedSquare,pairSingleCLM,lp.single_apply]

/-- Any scalar function recovering an analytic lift is analytic along
each squared tail coordinate. No continuity of the descended function or
nonvanishing of the lifted coordinate is assumed. -/
theorem analyticAt_mixedSquare_coordinate_of_recovery
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → ℂ) (g : (Coeff q × Coeff q) → ℂ)
    (V : Set (Coeff p × Coeff p)) (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hg : ∀ z ∈ V, g (pairMixedSquare S z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) (second : Bool) (k : ℤ) (hk : k ∉ S) :
    AnalyticAt ℂ (fun t => g (pairMixedSquare S z+pairSingleCLM q second k t)) 0 := by
  let a : ℂ := if second then z.2 k else z.1 k
  let lift : ℂ → (Coeff p × Coeff p) := fun w => z+pairSingleCLM p second k (w-a)
  let h : ℂ → ℂ := fun t => g (pairMixedSquare S z+pairSingleCLM q second k (t-a^2))
  have hl : AnalyticAt ℂ lift a :=
    analyticAt_const.add ((pairSingleCLM p second k).analyticAt _ |>.comp
      (analyticAt_id.sub analyticAt_const))
  have hla : lift a = z := by simp [lift]
  have hcomp : AnalyticAt ℂ (f ∘ lift) a := by
    apply AnalyticAt.comp (x := a) _ hl
    simpa only [hla] using hf z hz
  have ht : Tendsto lift (𝓝 a) (𝓝 z) := by simpa only [hla] using hl.continuousAt.tendsto
  have hpull : AnalyticAt ℂ (fun w => h (w^2)) a := by
    apply hcomp.congr
    filter_upwards [ht.eventually (hV.mem_nhds hz)] with w hw
    have he := hg (lift w) hw
    rw [pairMixedSquare_add_pairSingle S z second k hk w] at he
    exact he.symm
  have hdesc := ComplexAnalysis.analyticAt_of_comp_sq h a hpull
  have ha : AnalyticAt ℂ (fun t : ℂ => t+a^2) 0 := analyticAt_id.add analyticAt_const
  have hh : AnalyticAt ℂ h ((0 : ℂ)+a^2) := by simpa only [zero_add] using hdesc
  simpa only [Function.comp_def,h,add_sub_cancel_right] using
    hh.comp (f := fun t : ℂ => t+a^2) ha

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scalar linear observations of the continuous descent are analytic in
each tail square, also when that coordinate is zero. -/
theorem analyticAt_tailSquareDescent_tailCoordinate
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) (second : Bool) (k : ℤ) (hk : k ∉ S)
    (L : F →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun t => L (tailSquareDescent S f V
      (pairMixedSquare S z+pairSingleCLM q second k t))) 0 := by
  apply analyticAt_mixedSquare_coordinate_of_recovery (q := q) S (fun z => L (f z))
    (fun b => L (tailSquareDescent S f V b)) V hV
    (fun z hz => (L.analyticAt _).comp (hf z hz)) _ z hz second k hk
  intro w hw
  rw [tailSquareDescent_apply S f V hinv w hw]

/-- Every scalar observation is separately analytic in every retained or
squared coordinate of either component. -/
theorem analyticAt_tailSquareDescent_coordinate
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) (second : Bool) (k : ℤ)
    (L : F →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun t => L (tailSquareDescent S f V
      (pairMixedSquare S z+pairSingleCLM q second k t))) 0 := by
  classical
  by_cases hk : k ∈ S
  · have hh := analyticAt_tailSquareDescent_finiteHead (q := q) S f V hV hf hinv z hz
    have hi : AnalyticAt ℂ (pairSingleCLM q second k) 0 := (pairSingleCLM q second k).analyticAt 0
    have hh' : AnalyticAt ℂ (fun b : Coeff q × Coeff q =>
        tailSquareDescent S f V (pairMixedSquare S z+truncatePair S b))
        (pairSingleCLM q second k 0) := by simpa only [map_zero] using hh
    have he (t : ℂ) : truncatePair S (pairSingleCLM q second k t) = pairSingleCLM q second k t := by
      cases second <;> apply Prod.ext <;> ext n <;>
        by_cases hn : n = k <;> by_cases hs : n ∈ S <;>
        simp_all [truncatePair,pairSingleCLM,lp.single_apply]
    have hc := (L.analyticAt _).comp (hh'.comp (f := pairSingleCLM q second k) hi)
    simpa only [Function.comp_def,he] using hc
  · exact analyticAt_tailSquareDescent_tailCoordinate S f V hV hf hinv z hz second k hk L

end NLS.Coeff
