import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

import Mathlib.Tactic.LibrarySearch

open Complex Topology

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

/-- The wedge integral from z to w of a function f -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))



/-- diff of wedges -/
lemma diff_of_wedges {c : ℂ} {r : ℝ} (h0 : 0 < r) {z : ℂ} (hz : z ∈ Metric.ball c r)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∀ᶠ h in 𝓝 0,
      WedgeInt c (z+h) f - WedgeInt c z f = WedgeInt z (z+h) f := by
  simp only [Metric.mem_ball] at hz
  have : 0 < (r - dist z c) / 2 := by sorry
  filter_upwards [Metric.ball_mem_nhds 0 this]
  intro h hh
  simp only [Metric.mem_ball, dist_zero_right, norm_eq_abs] at hh
  simp only [WedgeInt] --, add_re, ofReal_add, add_im, smul_eq_mul]
  set intI := ∫ x : ℝ in c.re..(z + h).re, f (x + c.im * I)
  set intII := I • ∫ y : ℝ in c.im..(z + h).im, f ((z+h).re + y * I)
  set intIII := ∫ x : ℝ in c.re..z.re, f (x + c.im * I)
  set intIV := I • ∫ y : ℝ in c.im..z.im, f (z.re + y * I)
  set intV := ∫ x : ℝ in z.re..(z + h).re, f (x + z.im * I)
  set intVI := I • ∫ y : ℝ in z.im..(z + h).im, f ((z+h).re + y * I)
  let intVII := ∫ x : ℝ in z.re..(z+h).re, f (x + c.im * I)
  let intVIII := I • ∫ y : ℝ in c.im..z.im, f ((z+h).re + y * I)
  have intIdecomp : intI = intIII + intVII  := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply ContinuousOn.intervalIntegrable
      convert @ContinuousOn.comp ℝ ℂ ℂ _ _ _ f (fun x => (x : ℂ) + c.im * I) (Set.uIcc c.re z.re)
        ((fun (x : ℝ) => (x : ℂ) + c.im * I) '' (Set.uIcc c.re z.re)) ?_ ?_ ?_
      · convert @DifferentiableOn.continuousOn ℂ _ ℂ _ _ ℂ _ _ f _ _
        apply DifferentiableOn.mono hf
        sorry -- image of line is a subset of the disc
      · apply Continuous.continuousOn
        exact Continuous.comp (continuous_add_right _) continuous_ofReal
      · exact Set.mapsTo_image _ _
    sorry--integrable

  have intIIdecomp : intII = intVIII + intVI := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals]
    sorry--integrable
    sorry--integrable

  have rectZero : intVIII = - intVII + intV + intIV := by
    rw [← sub_eq_zero]
    have : intVII - intV + intVIII - intIV = 0 := by
      convert integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (z.re + c.im * I) ((z+h).re + z.im * I) ∅ ?_ ?_ ?_ using 4
      · simp
      · congr! 1 <;> simp
      · congr! 1 <;> simp
      · simp
      · simp
      · simp
      · simp
      · sorry -- ContinuousOn
      · intro x hx
        sorry -- differentiable
    rw [← this]
    ring

  rw [intIdecomp]
  rw [intIIdecomp]
  rw [rectZero]
  ring




lemma wedgeInt_of_const (z w c : ℂ) :
    WedgeInt z w (fun x => c) = c*(w-z) := by
  simp only [WedgeInt, intervalIntegral.integral_const, real_smul, ofReal_sub, smul_eq_mul]
  ext <;>
  simp only [add_re, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, sub_self, zero_mul,
sub_zero, I_re, I_im, mul_im, add_zero, one_mul, zero_sub, add_im,
zero_add]
   <;> ring


lemma deriv_of_wedgeInt {f: ℂ → ℂ} {U : Set ℂ} {hU: IsOpen U} (hf: ContinuousOn f U)
    {z₀ : ℂ} (hz₀ : z₀∈U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h ↦ ((WedgeInt z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by
  have : Asymptotics.IsLittleO (𝓝 0) (fun h ↦ f (z₀+h) - f z₀) (fun h ↦ (1:ℂ)) := by
    have := ContinuousOn.continuousAt hf (IsOpen.mem_nhds hU hz₀)
    have f_tendsto := ContinuousAt.tendsto this
    simp only [Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]

    -- shift the origin of the filter
    -- this can probably be done better
    let g := fun h ↦ z₀+h
    have g_tendsto : Filter.Tendsto g (𝓝 0) (𝓝 z₀) := by
      dsimp [g]
      rw [tendsto_sub_nhds_zero_iff.symm]
      simp only [add_sub_cancel']
      rw [Filter.tendsto_def]
      intros s hs
      simp only [Set.preimage_id']
      exact hs
    have := Filter.Tendsto.comp f_tendsto g_tendsto
    rw [Function.comp] at this
    exact this

  dsimp [WedgeInt]

  sorry







-- trivial case: empty set
theorem hasPrimitivesOfEmpty : hasPrimitives ∅ := by
  dsimp [hasPrimitives]
  simp only [Set.eqOn_empty, and_true]
  dsimp [DifferentiableOn]
  dsimp [DifferentiableWithinAt]
  dsimp [HasFDerivWithinAt]
  dsimp [HasFDerivAtFilter]
  simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
  forall_true_left]


-- To prove the main theorem, we first prove it on a disc
-- not sure what happens if U is empty
theorem hasPrimitivesOfConvex (U: Set ℂ) (hU: Convex ℝ U) : hasPrimitives U := by
  by_cases hne : U = ∅
  · convert hasPrimitivesOfEmpty

  · intros f hf_diff
    -- get z₀
    have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
    obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
    use fun z ↦ linint z₀ z f
    constructor
    · sorry

    · intro z  hz
      have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
        intros h hinU
        refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

        exact Subtype.mem z₀
      sorry


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
