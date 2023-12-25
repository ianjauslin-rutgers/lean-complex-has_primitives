import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Topology Set

set_option autoImplicit true

open scoped Interval

namespace Complex

/-- This lemma shows the equality between the convext hull of a complex product set and
  the complex product of convex hulls. -/
lemma convexHull_reProdIm (s t : Set ℝ) :
    convexHull ℝ (s ×ℂ t) = convexHull ℝ s ×ℂ convexHull ℝ t :=
  calc
    convexHull ℝ (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' (convexHull ℝ (s ×ˢ t)) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using equivRealProdLm.symm.toLinearMap.convexHull_image (s ×ˢ t)
    _ = convexHull ℝ s ×ℂ convexHull ℝ t := by rw [convexHull_prod]; rfl

lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. -/
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair,
    insert_union, ← insert_eq, Set.preimage_equiv_eq_image_symm, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. -/
theorem rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ U := by
  rw [segment_reProdIm_segment_eq_convexHull]
  convert convexHull_min ?_ (U_convex)
  refine Set.insert_subset hz (Set.insert_subset hzw (Set.insert_subset hwz ?_))
  exact Set.singleton_subset_iff.mpr hw

/-- If `z` is in a ball centered at `c`, then `z.re + c.im * I` is in the ball. -/
lemma cornerRectangle_in_disc {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ Metric.ball c r) :
    z.re + c.im * I ∈ Metric.ball c r := by
  simp only [Metric.mem_ball] at hz ⊢
  rw [Complex.dist_of_im_eq] <;> simp only [add_re, I_re, mul_zero, I_im, zero_add, add_im,
    add_zero, sub_self, mul_re, mul_one, ofReal_im, mul_im, ofReal_re]
  apply lt_of_le_of_lt ?_ hz
  rw [Complex.dist_eq_re_im, Real.dist_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [_root_.sq_abs, le_add_iff_nonneg_right, ge_iff_le, sub_nonneg]
  exact sq_nonneg _

end Complex

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
theorem horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun x => ↑x + ↑b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', Set.mem_preimage, Set.mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
theorem verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun y => ↑a + ↑y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', Set.mem_preimage, Set.mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, Set.mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

/-- A set `U` `HasPrimitives` if, every holomorphic function on `U` has a primitive -/
def HasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z

/-- The wedge integral from `z` to `w` of a function `f` -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-- A function `f` `VanishesOnRectanglesInDisc` if, for any rectangle contained in a disc,
  the integral of `f` over the rectangle is zero. -/
def VanishesOnRectanglesInDisc (c : ℂ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
    ∀ z w, z ∈ Metric.ball c r → w ∈ Metric.ball c r → (z.re + w.im * I) ∈ Metric.ball c r →
    (w.re + z.im * I) ∈ Metric.ball c r →
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I) = 0

/-- If a function `f` `VanishesOnRectanglesInDisc` of center `c`, then, for all `w` in a
  neighborhood of `z`, the wedge integral from `c` to `w` minus the wedge integral from `c` to `z`
  is equal to the wedge integral from `z` to `w`. -/
lemma VanishesOnRectanglesInDisc.diff_of_wedges {c : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ Metric.ball c r) {f : ℂ → ℂ} (f_cont : ContinuousOn f (Metric.ball c r))
    (hf : VanishesOnRectanglesInDisc c r f) :
    ∀ᶠ (w : ℂ) in 𝓝 z,
      WedgeInt c w f - WedgeInt c z f = WedgeInt z w f := by
  let r₁ := (r - dist z c) / 2
  have hr₁ : 0 < r₁
  · simp only [Metric.mem_ball, gt_iff_lt] at hz ⊢
    linarith
  have z_ball : Metric.ball z r₁ ⊆ Metric.ball c r
  · intro w hw
    simp only [Metric.mem_ball] at hw hz ⊢
    have := dist_triangle w z c
    nlinarith
  filter_upwards [Metric.ball_mem_nhds z hr₁]
  intro w w_in_z_ball
  have hzPlusH : w ∈ Metric.ball c r := Set.mem_of_subset_of_mem z_ball w_in_z_ball
  simp only [WedgeInt]
  set intI := ∫ x : ℝ in c.re..(w).re, f (x + c.im * I)
  set intII := I • ∫ y : ℝ in c.im..w.im, f (w.re + y * I)
  set intIII := ∫ x : ℝ in c.re..z.re, f (x + c.im * I)
  set intIV := I • ∫ y : ℝ in c.im..z.im, f (z.re + y * I)
  set intV := ∫ x : ℝ in z.re..w.re, f (x + z.im * I)
  set intVI := I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I)
  let intVII := ∫ x : ℝ in z.re..w.re, f (x + c.im * I)
  let intVIII := I • ∫ y : ℝ in c.im..z.im, f (w.re + y * I)
  have integrableHoriz : ∀ a₁ a₂ b : ℝ, a₁ + b * I ∈ Metric.ball c r → a₂ + b * I ∈ Metric.ball c r →
    IntervalIntegrable (fun x => f (x + b * I)) MeasureTheory.volume a₁ a₂
  · intro a₁ a₂ b ha₁ ha₂
    apply ContinuousOn.intervalIntegrable
    convert ContinuousOn.comp (g := f) (f := fun (x : ℝ) => (x : ℂ) + b * I) (s := Set.uIcc a₁ a₂)
      (t := (fun (x : ℝ) => (x : ℂ) + b * I) '' (Set.uIcc a₁ a₂)) ?_ ?_ (Set.mapsTo_image _ _)
    · apply f_cont.mono
      convert rectangle_in_convex (convex_ball c r) ha₁ ha₂ ?_ ?_ using 1 <;>
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add, ha₁, ha₂]
      simp only [le_refl, uIcc_of_le, Icc_self, horizontalSegment_eq a₁ a₂ b]
    · exact Continuous.continuousOn (Continuous.comp (continuous_add_right _) continuous_ofReal)
  have integrableVert : ∀ a b₁ b₂ : ℝ, a + b₁ * I ∈ Metric.ball c r → a + b₂ * I ∈ Metric.ball c r
    → IntervalIntegrable (fun y => f (a + y * I)) MeasureTheory.volume b₁ b₂
  · intro a b₁ b₂ hb₁ hb₂
    apply ContinuousOn.intervalIntegrable
    convert ContinuousOn.comp (g := f) (f := fun (y : ℝ) => (a : ℂ) + y * I) (s := Set.uIcc b₁ b₂)
      (t := (fun (y : ℝ) => (a : ℂ) + y * I) '' (Set.uIcc b₁ b₂)) ?_ ?_ (Set.mapsTo_image _ _)
    · apply f_cont.mono
      convert rectangle_in_convex (convex_ball c r) hb₁ hb₂ ?_ ?_ using 1 <;>
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add, hb₁, hb₂]
      simp only [ le_refl, Set.uIcc_of_le, Set.Icc_self, verticalSegment_eq a b₁ b₂]
    · apply Continuous.continuousOn
      exact ((continuous_add_left _).comp (continuous_mul_right _)).comp continuous_ofReal
  have intIdecomp : intI = intIII + intVII
  · rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simp only [re_add_im, Metric.mem_ball, dist_self, hr]
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hzPlusH
  have intIIdecomp : intII = intVIII + intVI
  · rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact cornerRectangle_in_disc hzPlusH
    · apply Set.mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · apply Set.mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · convert hzPlusH using 1; ext <;> simp
  have rectZero : intVIII = - intVII + intV + intIV
  · rw [← sub_eq_zero]
    have : intVII - intV + intVIII - intIV = 0 := by
      convert hf (z.re + c.im * I) (w.re + z.im * I) (cornerRectangle_in_disc hz) ?_ ?_ ?_ using 2
      · congr! 1 <;> simp
      · simp
      · apply Set.mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
      · convert hz using 1; ext <;> simp
      · convert cornerRectangle_in_disc hzPlusH using 1; ext <;> simp
    rw [← this]
    ring
  rw [intIdecomp, intIIdecomp, rectZero]
  ring







lemma wedgeInt_of_const (z w c : ℂ) :
    WedgeInt z w (fun x => c) = c*(w-z) := by
  simp only [WedgeInt, intervalIntegral.integral_const, real_smul, ofReal_sub, smul_eq_mul]
  ext <;>
  simp only [add_re, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, sub_self, zero_mul,
sub_zero, I_re, I_im, mul_im, add_zero, one_mul, zero_sub, add_im,
zero_add]
   <;> ring



lemma deriv_of_linint {f: ℝ → ℂ} {a: ℝ} {U : Set ℝ} (hU: IsOpen U) (hUa: a∈ U) (hf: ContinuousOn f U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h ↦ ((∫ x in a..a+h, f x) - h*(f a))) (fun h ↦ h) := by

  sorry

lemma deriv_of_horv_0 {f:ℝ →ℂ} {U: Set ℝ} {hU0: 0 ∈ U} {hU: IsOpen U}
    (hfC: ContinuousOn f U) (hfM: StronglyMeasurableAtFilter f (nhds 0))
    {c : ℝ} (hc: 0<c):
    ∀ᶠ (h : ℝ) in 𝓝 0, ‖(∫ (x : ℝ) in (0:ℝ)..h, f x) - h * f 0‖ ≤ c/3 * ‖h‖ := by

  have integrable : IntervalIntegrable (fun x:ℝ => f x-f 0) Real.measureSpace.volume 0 0 := by
    simp
  have continuous_on : ContinuousOn (fun x => f x - f 0) U := by
    apply ContinuousOn.sub hfC (continuousOn_const)
  have continuous : ContinuousAt (fun x => f x - f 0) 0 := by
    apply ContinuousOn.continuousAt continuous_on ?_
    rw [mem_nhds_iff]
    use U
  have measurable : StronglyMeasurableAtFilter (fun x => f x - f 0) (nhds 0) := by
    apply ContinuousOn.stronglyMeasurableAtFilter hU continuous_on 0
    exact hU0

  have diff := intervalIntegral.integral_hasDerivAt_right integrable measurable continuous
  rw [hasDerivAt_iff_isLittleO] at diff
  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, sub_self, real_smul, ofReal_sub, mul_zero] at diff
  rw [Asymptotics.isLittleO_iff] at diff
  have : 0 < c/3 := div_pos hc zero_lt_three
  have := diff this

  -- condition on h
  rw [Filter.eventually_iff] at this
  filter_upwards [this]
  intro h h_diff

  simp only [ofReal_zero, add_zero, re_add_im, sub_self, mul_zero, sub_zero, norm_eq_abs, Real.norm_eq_abs] at h_diff

  -- write f as f-f(z₀)+f(z₀)
  calc
    _ = ‖(∫ x in (0:ℝ)..h, ((f x-f 0) + f 0)) - h*f 0‖ := by ring_nf
    _ = ‖(∫ x in (0:ℝ)..h, (f x-f 0)) + (∫ x in (0:ℝ)..h, f 0) - h* f 0‖ := ?_
    _ = ‖(∫ x in (0:ℝ)..h, (f x-f 0)) + h•f 0 - h* f 0‖ := by
      rw [intervalIntegral.integral_const (f 0)]
      simp
    _ = ‖(∫ x in (0:ℝ)..h, (f x-f 0))‖ := by simp
    _ = Complex.abs ((∫ (x : ℝ) in (0:ℝ)..h, f x - f 0)) := by simp
    _ ≤ _ := h_diff
  congr

  rw [intervalIntegral.integral_add ?_ ?_]
  · sorry
  · sorry



lemma deriv_of_horv (a:ℝ) {f:ℝ →ℂ} {U: Set ℝ} {hUa: a ∈ U} {hU: IsOpen U}
    (hfC: ContinuousOn f U) (hfM: StronglyMeasurableAtFilter f (nhds a))
    (c : ℝ) (hc: 0<c):
    ∀ᶠ (h : ℝ) in 𝓝 0, ‖(∫ (x : ℝ) in a..a+h, f x) - h * f a‖ ≤ c/3 * ‖h‖ := by
  let U' := {x:ℝ | x+a ∈ U}
  have continuous : ContinuousOn (fun x => f (a+x)) U' := by
    sorry
  have measurable : StronglyMeasurableAtFilter (fun x => f (a+x)) (nhds 0) := by
    sorry
  have := @deriv_of_horv_0 _ _ ?_ ?_ continuous measurable _ hc
  simp_rw [intervalIntegral.integral_comp_add_left (fun x:ℝ => f x) a] at this
  simp only [add_zero, sub_self, mul_zero, sub_zero] at this
  exact this

  simp only [Set.mem_setOf_eq, zero_add]
  exact hUa

  sorry


lemma deriv_of_wedgeInt' {f: ℂ → ℂ} {U : Set ℂ} {hU: IsOpen U} (hf: ContinuousOn f U)
    {z₀ : ℂ} (hz₀ : z₀∈U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ((WedgeInt z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by
  sorry
  -- simp [WedgeInt]
  -- -- turn littleO into bigO
  -- rw [Asymptotics.isLittleO_iff]
  -- intro c hc

  -- -- get ball around z₀
  -- obtain ⟨ε,hε,B⟩ := (Metric.isOpen_iff.mp hU) z₀ hz₀

  -- -- restate goal, splitting real and imaginary parts of h
  -- have : ∀ᶠ (hre : ℝ) in 𝓝 0, ∀ᶠ(him : ℝ) in 𝓝 0,
  -- ‖((∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) +
  --         I * ∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I)) -
  --       (hre+him*I) * f z₀‖ ≤
  --   c * ‖hre+him*I‖ := by
    -- -- apply fundamental theorem of calculus to horizontal part
    -- have continuous_h : ContinuousOn (fun x:ℝ => f (x + z₀.im*I)) z₀.re := by
    --   sorry
    -- have stronglymeasurable_h : StronglyMeasurableAtFilter (fun x:ℝ => f (x + z₀.im*I)) (nhds z₀.re) := by
    --   sorry
    -- have horizontal := deriv_of_horv z₀.re  continuous_h stronglymeasurable_h c hc

    -- -- condition on h.re
    -- rw [Filter.eventually_iff] at horizontal
    -- filter_upwards [Metric.ball_mem_nhds 0 hε,horizontal]
    -- intro hre hre_eps hre_diff

    -- -- apply fundamental theorem of calculus to vertical part
    -- have continuous_v : ContinuousAt (fun y:ℝ => f (z₀.re + hre + y*I)) z₀.im := by
    --   sorry
    -- have stronglymeasurable_v : StronglyMeasurableAtFilter (fun y:ℝ => f (z₀.re + hre + y*I)) (nhds z₀.im) := by
    --   sorry
    -- have vertical := deriv_of_horv z₀.im  continuous_v stronglymeasurable_v c hc

    -- -- condition on h.im
    -- rw [Filter.eventually_iff] at vertical
    -- filter_upwards [Metric.ball_mem_nhds 0 hε,vertical]
    -- intro him him_eps him_diff

    -- have : ‖((∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) +
    --     I * ∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I)) -
    --     (↑hre + ↑him * I) * f z₀‖ ≤
    --     ‖(∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) - hre * f z₀‖ +
    --     ‖(∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I) - ↑him * f (z₀+hre))‖
    --     + ‖I* (f (z₀+hre) - f z₀)‖ := by
    --   -- norm_add_le
    --   sorry

    -- suffices hsp : ‖(∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) - hre * f z₀‖ +
    --     ‖(∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I) - ↑him * f (z₀+hre))‖
    --     + ‖I* (f (z₀+hre) - f z₀)‖ ≤ c*‖hre + him*I‖

    -- · exact le_trans this hsp
    -- · sorry


--  -- write f as f-f(z₀)+f(z₀)
--  have : ∀ h:ℂ, ∫ x in z₀.re..z₀.re + h.re, f (x + z₀.im * I) = ∫ x in z₀.re..z₀.re + h.re, ((f (x + z₀.im * I)-f z₀) + f z₀) := by
--    intro h
--    ring_nf
--  have : ∀ h:ℂ, ∫ x in z₀.re..z₀.re + h.re, f (x + z₀.im * I) = (∫ x in z₀.re..z₀.re + h.re, (f (x + z₀.im * I)-f z₀)) + h.re*f z₀ := by
--    intro h
--    sorry
--  conv =>
--    lhs
--    intro h
--    rw [this]
--
--  -- write f as f-f(z₀)+f(z₀)
--  have : ∀ h:ℂ, ∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) = ∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) -f z₀) + f z₀ := by
--    intro h
--    ring_nf
--  have : ∀ h:ℂ, ∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) = (∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) -f z₀) + h.im * f z₀ := by
--    intro h
--    sorry
--  conv =>
--    lhs
--    intro h
--    rw [this]
--
--  -- why doesn't this work??
----  conv =>
----    lhs
----    intro h
----    pattern h * f z₀
----    rw [(Complex.re_add_im h).symm]
----  ring_nf
--  have : ∀ h : ℂ, h*f z₀ = (h.re+h.im*I)*f z₀ := by
--    intro h
--    simp
--  conv =>
--    lhs
--    intro h
--    rw [this h]
--
--  -- why doesn't ring do this on its own?!?!?!?!
--  have : ∀ h:ℂ, (∫ (x : ℝ) in z₀.re..z₀.re + h.re, f (↑x + ↑z₀.im * I) - f z₀) + ↑h.re * f z₀ +
--        I * ((∫ (y : ℝ) in z₀.im..z₀.im + h.im, f (↑z₀.re + ↑h.re + ↑y * I) - f z₀) + ↑h.im * f z₀) -
--      (↑h.re + ↑h.im * I) * f z₀ = (∫ (x : ℝ) in z₀.re..z₀.re + h.re, f (↑x + ↑z₀.im * I) - f z₀) +
--        I * ((∫ (y : ℝ) in z₀.im..z₀.im + h.im, f (↑z₀.re + ↑h.re + ↑y * I) - f z₀)) := by
--    intro h
--    ring
--  conv =>
--    lhs
--    intro h
--    rw [this h]
--
--  -- apply fundamental theorem of calculus to each part of the integral
--  have continuous_h : ContinuousAt (fun x:ℝ => f (x + z₀.im*I)-f z₀) z₀.re := by
--    sorry
--  have integrable_h : IntervalIntegrable (fun x:ℝ => f (x + z₀.im*I)-f z₀) Real.measureSpace.volume z₀.re z₀.re := by
--    sorry
--  have stronglymeasureable_h : StronglyMeasurableAtFilter (fun x:ℝ => f (x + z₀.im*I)-f z₀) (nhds z₀.re) := by
--    sorry
--
--  have diff_h := intervalIntegral.integral_hasDerivAt_right integrable_h stronglymeasureable_h continuous_h
--  rw [hasDerivAt_iff_isLittleO] at diff_h
--  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, sub_self, real_smul, ofReal_sub, mul_zero] at diff_h




  -- -- apply fundamental theorem of calculus to each part of the integral
  -- have horint : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ∫ x in z₀.re..z₀.re + h.re, (f (x + z₀.im * I) - f z₀)) (fun h => h) := by
  --   have integrable : IntervalIntegrable (fun x:ℝ => f (x + z₀.im*I)-f z₀) z₀.re z₀.re+h.re
  -- have verint : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) - f z₀)) (fun h => h) := by
  --   sorry
  -- have verint' : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ I*∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) - f z₀)) (fun h => h) :=
  --   Asymptotics.IsLittleO.const_mul_left verint I

  -- exact Asymptotics.IsLittleO.add horint verint'

  --have : Asymptotics.IsLittleO (𝓝 0) (fun h ↦ f (z₀+h) - f z₀) (fun h ↦ (1:ℂ)) := by
  --  have := ContinuousOn.continuousAt hf (IsOpen.mem_nhds hU hz₀)
  --  have f_tendsto := ContinuousAt.tendsto this
  --  simp only [Asymptotics.isLittleO_one_iff]
  --  rw [tendsto_sub_nhds_zero_iff]

  --  -- shift the origin of the filter
  --  -- this can probably be done better
  --  let g := fun h ↦ z₀+h
  --  have g_tendsto : Filter.Tendsto g (𝓝 0) (𝓝 z₀) := by
  --    dsimp [g]
  --    rw [tendsto_sub_nhds_zero_iff.symm]
  --    simp only [add_sub_cancel']
  --    rw [Filter.tendsto_def]
  --    intros s hs
  --    simp only [Set.preimage_id']
  --    exact hs
  --  have := Filter.Tendsto.comp f_tendsto g_tendsto
  --  rw [Function.comp] at this
  --  exact this

  --dsimp [WedgeInt]







-- -- trivial case: empty set
-- theorem HasPrimitivesOfEmpty : HasPrimitives ∅ := by
--   dsimp [HasPrimitives]
--   simp only [Set.eqOn_empty, and_true]
--   dsimp [DifferentiableOn]
--   dsimp [DifferentiableWithinAt]
--   dsimp [HasFDerivWithinAt]
--   dsimp [HasFDerivAtFilter]
--   simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
--   forall_true_left]

-- example (f g : ℂ → ℂ) (hf : ∀ᶠ (x:ℂ) in 𝓝 0, f x = 2) (hg : ∀ᶠ (x : ℂ) in 𝓝 0, g x = 3) : ∀ᶠ (x : ℂ) in 𝓝 0, f x * g x = 6 := by
--   filter_upwards [hf, hg]
--   intro x hf hg
--   rw [hf, hg]
--   ring

theorem deriv_of_wedgeInt''' {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball c r)) (hf₂ : VanishesOnRectanglesInDisc c r f)
    {z : ℂ} (hz : z ∈ Metric.ball c r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (w : ℂ) in 𝓝 z, ‖WedgeInt z w f - (w - z) * f z‖ ≤ ε * ‖w - z‖ := by
  sorry

theorem deriv_of_wedgeInt'' {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball c r)) (hf₂ : VanishesOnRectanglesInDisc c r f)
    {z : ℂ} (hz : z ∈ Metric.ball c r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (w : ℂ) in 𝓝 z, ‖WedgeInt c w f - WedgeInt c z f - (w - z) * f z‖ ≤ ε * ‖w - z‖ := by
  have diff_wedge := hf₂.diff_of_wedges hr hz hf
  rw [Filter.eventually_iff] at diff_wedge
  have := deriv_of_wedgeInt''' hr hf hf₂ hz hε
  rw [Filter.eventually_iff] at this
  filter_upwards [diff_wedge, this]
  intro w hw hww
  rwa [hw]

theorem deriv_of_wedgeInt''''' {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball c r)) (hf₂ : VanishesOnRectanglesInDisc c r f)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    deriv (fun z ↦ WedgeInt c z f) z = f z := by
  dsimp [deriv]
  sorry

-- theorem DifferentiableOn_WedgeInt {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
--     (hf : ContinuousOn f (Metric.ball c r))
--     (hf₂ : VanishesOnRectanglesInDisc c r f) : DifferentiableOn ℂ (fun z ↦ WedgeInt c z f) (Metric.ball c r) := by
--   intro z hz
--   use (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (f z))
--   rw [hasFDerivWithinAt_iff_hasDerivWithinAt]
--   dsimp [HasDerivWithinAt, HasDerivAtFilter, HasFDerivAtFilter]
--   simp only [one_mul]
--   rw [Asymptotics.IsLittleO_def]
--   intro ε h_ε
--   rw [Asymptotics.isBigOWith_iff]
--   apply eventually_nhdsWithin_of_eventually_nhds
--   exact deriv_of_wedgeInt'' hr hf hf₂ hz h_ε


-- ADDING 12/18/23 from Heather
-- Put near `derivWithin_zero_of_nmem_closure`
theorem hasDerivWithinAt_of_nmem_closure {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : F} {s : Set 𝕜}
    (h : x ∉ closure s) : HasDerivWithinAt f f' s x := sorry
--  .of_nhdsWithin_eq_bot <| eq_bot_mono (nhdsWithin_mono _ (diff_subset _ _)) <| by
--    rwa [mem_closure_iff_nhdsWithin_neBot, not_neBot] at h
-- #exit
--   rw [HasDerivWithinAt, HasDerivAtFilter]
--   apply fderivWithin_zero_of_isolated



theorem deriv_of_wedgeInt {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball c r)) (hf₂ : VanishesOnRectanglesInDisc c r f)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    HasDerivAt (fun w => WedgeInt c w f) (f z) z := by
  sorry

/-- Moreira's theorem
/%%
This is Moreira's theorem.
\begin {theorem}[Moreira's theorem]
\label {moreira}
\lean {moreira}\leanok
Let $f$ be a continuous function on a disc $D(c,r)$, and suppose that $f$ vanishes on rectangles in $D(c,r)$. Then $f$ has a primitive on $D(c,r)$.
\end {theorem}
%%/
-/
theorem moreiras_theorem {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball c r))
    (hf₂ : VanishesOnRectanglesInDisc c r f) :
    ∃ g : ℂ → ℂ, ∀ z ∈ (Metric.ball c r), HasDerivAt g (f z) z :=
  ⟨fun z ↦ WedgeInt c z f, fun _ hz ↦ deriv_of_wedgeInt hr hf hf₂ hz⟩


theorem vanishesOnRectangles_of_holomorphic {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    VanishesOnRectanglesInDisc c r f := by
  intro z w hz hw hz' hw'
  --%% Given a rectangle in the disc, we want to show that the integral over the rectangle is zero.
  convert integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ ?_ ?_ ?_ using 4
  · simp
  · apply (hf.mono _).continuousOn
    intro x hx
    exact Set.mem_of_mem_of_subset hx (rectangle_in_convex (convex_ball c r) hz hw hz' hw')
  · intro x hx
    apply hf.differentiableAt
    rw [mem_nhds_iff]
    refine ⟨Metric.ball c r, Eq.subset rfl, Metric.isOpen_ball, ?_⟩
    apply Set.mem_of_mem_of_subset ?_ (rectangle_in_convex (convex_ball c r) hz hw hz' hw')
    simp only [ge_iff_le, gt_iff_lt, lt_max_iff, min_lt_iff, lt_self_iff_false, false_or, or_false,
      lt_or_lt_iff_ne, ne_eq, not_not, le_min_iff, max_le_iff, le_refl, true_and, and_true,
      diff_empty] at hx
    apply Set.mem_of_mem_of_subset hx

    sorry -- rectangle is inside disc




-- To prove the main theorem, we first prove it on a disc
theorem hasPrimitives_of_disc (c : ℂ) {r : ℝ} (hr : 0 < r) : HasPrimitives (Metric.ball c r) :=
  fun _ hf ↦ moreiras_theorem hr hf.continuousOn (vanishesOnRectangles_of_holomorphic hr hf)

  -- by_cases hne : U = ∅
  -- · convert HasPrimitivesOfEmpty

  -- · intros f hf_diff
  --   -- get z₀
  --   have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
  --   obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
  --   use fun z ↦ linint z₀ z f
  --   constructor
  --   · sorry

  --   · intro z  hz
  --     have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
  --       intros h hinU
  --       refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

  --       exact Subtype.mem z₀
  --     sorry





-- theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
--   refine straightSeg t₁ t₂ ht z₁ z₂
--   sorry
