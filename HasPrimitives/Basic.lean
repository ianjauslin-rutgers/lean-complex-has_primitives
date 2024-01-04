import Mathlib.Analysis.Complex.CauchyIntegral

/-%%
This project aims to formalize a proof that holomorphic functions on discs have primitives.
%%-/

open Complex Topology Set Metric

set_option autoImplicit true

open scoped Interval

namespace Asymptotics

variable {α : Type*} {E : Type*} {F : Type*} [NormedAddGroup E] [Norm F]

variable {f g : α → E} {h : α → F} {l : Filter α}

/--
  We write `f =ᵤ g upto O[l] h` to mean that `f - g =O[l] h`. We call this `EqUpToBigO`
-/
notation:100 f " =ᵤ " g "upto O[" l "]" h :100 => IsBigO l (f - g) h

lemma EqUpToBigO_apply :
    (f =ᵤ g upto O[l] h) ↔ (IsBigO l (f - g) h) := by rfl

lemma EqUpToBigO.trans {k : α → E}
    (hfg : f =ᵤ g upto O[l] h)
    (hgk : g =ᵤ k upto O[l] h) :
    f =ᵤ k upto O[l] h := by
  rw [IsBigO] at hfg hgk ⊢
  obtain ⟨c₁, hc₁⟩ := hfg
  obtain ⟨c₂, hc₂⟩ := hgk
  use c₁ + c₂
  rw [IsBigOWith] at hc₁ hc₂ ⊢
  filter_upwards [hc₁, hc₂]
  intro x _ _
  calc
    _ = ‖(f - g) x + (g - k) x‖ := by simp
    _ ≤ ‖(f - g) x‖ + ‖(g - k) x‖ := by apply norm_add_le
    _ ≤ c₁ * ‖h x‖ + c₂ * ‖h x‖ := by linarith
    _ = _ := by ring

/--
  We write `f =ᵤ g upto o[l] h` to mean that `f - g =o[l] h`. We call this `EqUpToLittleO`
-/
notation:100 f " =ᵤ " g "upto o[" l "]" h :100 => IsLittleO l (f - g) h

lemma EqUpToLittleO_apply :
    (f =ᵤ g upto o[l] h) ↔ (IsLittleO l (f - g) h) := by rfl

lemma EqUpToLittleO.trans {k : α → E}
    (hfg : f =ᵤ g upto o[l] h)
    (hgk : g =ᵤ k upto o[l] h) :
    f =ᵤ k upto o[l] h := by
  rw [IsLittleO] at hfg hgk ⊢
  intro ε ε_pos
  have hfgε := @hfg (ε/2) (by linarith)
  have hgkε := @hgk (ε/2) (by linarith)
  rw [IsBigOWith] at hfgε hgkε ⊢
  filter_upwards [hfgε, hgkε]
  intro x _ _
  calc
    _ = ‖(f - g) x + (g - k) x‖ := by simp
    _ ≤ ‖(f - g) x‖ + ‖(g - k) x‖ := by apply norm_add_le
    _ ≤ ε / 2 * ‖h x‖ + ε / 2 * ‖h x‖ := by linarith
    _ = _ := by ring

end Asymptotics

namespace Set

-- TO DO: move to `Mathlib.Data.Intervals.UnorderedInterval` (Yael add API?)
def uIoo {α : Type*} [LinearOrder α]  : α → α → Set α := fun a b => Ioo (a ⊓ b) (a ⊔ b)

-- TO DO: move to `Mathlib.Data.Intervals.UnorderedInterval` (Yael add API?)
theorem uIoo_comm {α : Type*} [LinearOrder α] (a : α) (b : α) :
    uIoo a b = uIoo b a := by simp [uIoo, inf_comm, sup_comm]

theorem uIoo_subset_uIcc {α : Type*} [LinearOrder α] (a : α) (b : α) :
    uIoo a b ⊆ uIcc a b := by simp [uIoo, uIcc, Ioo_subset_Icc_self]

end Set

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

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
theorem reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
theorem reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. -/
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair,
    insert_union, ← insert_eq, preimage_equiv_eq_image_symm, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-%%
\begin{definition}[Rectangle]
  \label{Rectangle}
  \lean{Rectangle}\leanok
    Given points $z$ and $w$ in $\mathbb C$, a ``Rectangle'' means an axis-parallel rectangle with
    corners $z$ and $w$.
\end{definition}
%%-/
/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. -/
theorem rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  convert convexHull_min ?_ (U_convex)
  refine insert_subset hz (insert_subset hzw (insert_subset hwz ?_))
  exact singleton_subset_iff.mpr hw

/-- If `z` is in a ball centered at `c`, then `z.re + c.im * I` is in the ball. -/
lemma cornerRectangle_in_disc {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    z.re + c.im * I ∈ ball c r := by
  simp only [mem_ball] at hz ⊢
  rw [dist_of_im_eq] <;> simp only [add_re, I_re, mul_zero, I_im, zero_add, add_im,
    add_zero, sub_self, mul_re, mul_one, ofReal_im, mul_im, ofReal_re]
  apply lt_of_le_of_lt ?_ hz
  rw [dist_eq_re_im, Real.dist_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [_root_.sq_abs, le_add_iff_nonneg_right, ge_iff_le, sub_nonneg]
  exact sq_nonneg _

/-- As `w → z`, `w.re - z.re` is big-O of `w - z`. -/
theorem re_isBigO {z : ℂ} :
  (fun (w : ℂ) => w.re - z.re) =O[𝓝 z] fun w => w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, Complex.norm_eq_abs, one_mul]
  rw [← Complex.sub_re]
  exact Complex.abs_re_le_abs (w - z)

/-- As `w → z`, `w.im - z.im` is big-O of `w - z`. -/
theorem im_isBigO {z : ℂ} :
  (fun (w : ℂ) => w.im - z.im) =O[𝓝 z] fun w => w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, Complex.norm_eq_abs, one_mul]
  rw [← Complex.sub_im]
  exact Complex.abs_im_le_abs (w - z)

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
theorem horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun x => ↑x + ↑b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
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
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Complex

namespace Metric

/-- If `z` is in a ball centered at `c` with radius `r`, then the ball centered at `z` with radius
  `r - dist z c` is contained in the original ball. -/
theorem ball_subset_ball₁ {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    ball z (r - dist z c) ⊆ ball c r := by
  intro w hw
  simp only [mem_ball] at hw hz ⊢
  nlinarith [dist_triangle w z c]

end Metric

namespace Complex

/-%%
\begin{definition}[Has Primitives]
  \label{HasPrimitives}
  \lean{HasPrimitives}\leanok
  Given a set $U\subset\mathbb C$, for any differentiable $f:U\to\mathbb C$, there exists a differentiable $g:U\to\mathbb C$ such that $g'=f$ on $U$.
\end{definition}
%%-/
/-- A set `U` `HasPrimitives` if, every holomorphic function on `U` has a primitive -/
def HasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z


/-%%
A wedge is the union of a horizontal line and a vertical line.

\begin{definition}[Wedge Integral]
  \label{WedgeInt}
  \lean{WedgeInt}\leanok
  \uses{linint}
  Given $z,w\in\mathbb C$ and a function $f:\mathbb C\to\mathbb C$, the wedge integral from $z$ to $w$ is defined as the sum of two complex integrals, one along the horizontal path from $z$ to $\Re(w)+i \Im(z)$, and another along a vertical path from there to $w$,
   \begin{equation}
      \int_{z\to_W\  w} f(x)\ dx
      :=
      \int_{\Re(z)}^{\Re(w)} f(x+i\Im(z))\ dx
      +
      i\int_{\Im(z)}^{\Im(w)} f(\Re(w)+iy)\ dy
      .
   \end{equation}
\end{definition}
%%-/
/-- The wedge integral from `z` to `w` of a function `f` -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-%%
A ``Rectangle Integral'' is what it sounds like.

\begin{definition}[Rectangle Integral]
  \label{RectangleIntegral}
  \lean{RectangleIntegral}\leanok
  Given $z,w\in\mathbb C$ and a function $f:\mathbb C\to\mathbb C$, the rectangle integral is defined as the sum of four complex integrals:
   \begin{equation}
      \int_{R(z,w)} f(x)\ dx
      :=
      \int_{\Re(z)}^{\Re(w)} f(x+i\Im(z))\ dx
      -
      \int_{\Re(z)}^{\Re(w)} f(x+i\Im(w))\ dx
      +
      i\int_{\Im(z)}^{\Im(w)} f(\Re(w)+iy)\ dy
      -
      i\int_{\Im(z)}^{\Im(w)} f(\Re(z)+iy)\ dy
      .
   \end{equation}
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-%%
We say that a function $f$ ``vanishes on rectangles in a disc'', $D(c,r)$ if, for any rectangle contained in $D(c,r)$, the integral of $f$ over the rectangle is zero.
\begin{definition}[Vanishes On Rectangles In Disc]
  \label{VanishesOnRectanglesInDisc}
  \lean{VanishesOnRectanglesInDisc}\leanok
  A function $f:\mathbb C\to\mathbb C$ vanishes on rectangles in a disc $D(c,r)$ if, for any rectangle $R(z,w)$ contained in $D(c,r)$, the integral of $f$ over the rectangle is zero.
\end{definition}
%%-/
/-- A function `f` `VanishesOnRectanglesInDisc` if, for any rectangle contained in a disc,
  the integral of `f` over the rectangle is zero. -/
def VanishesOnRectanglesInDisc (c : ℂ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
    ∀ z w, z ∈ ball c r → w ∈ ball c r → (z.re + w.im * I) ∈ ball c r →
    (w.re + z.im * I) ∈ ball c r → RectangleIntegral f z w = 0

/-%%
If a function $f$ vanishes on rectangles in a disc $D(c,r)$, then, for any $w$ in a neighborhood of $z$ in $D(c,r)$, the wedge integral from $c$ to $w$ minus the wedge integral from $c$ to $z$ is equal to the wedge integral from $z$ to $w$. This is the key lemma in the proof of the existence of primitives.
\begin{lemma}[Wedge Integral Difference]
  \label{diff_of_wedges}
  \lean{VanishesOnRectanglesInDisc.diff_of_wedges}\leanok
  \uses{VanishesOnRectanglesInDisc}
  If a function $f$ vanishes on rectangles in a disc $D(c,r)$, then, for any $w$ in a neighborhood of $z$ in $D(c,r)$,
  $$
    \int_{c\to_W\  w} f(x)\ dx
    -
    \int_{c\to_W\  z} f(x)\ dx
    =
    \int_{z\to_W\  w} f(x)\ dx
    .
  $$
\end{lemma}
%%-/
/-- If a function `f` `VanishesOnRectanglesInDisc` of center `c`, then, for all `w` in a
  neighborhood of `z`, the wedge integral from `c` to `w` minus the wedge integral from `c` to `z`
  is equal to the wedge integral from `z` to `w`. -/
lemma VanishesOnRectanglesInDisc.diff_of_wedges {c : ℂ} {r : ℝ} {z : ℂ}
    (hz : z ∈ ball c r) {f : ℂ → ℂ} (f_cont : ContinuousOn f (ball c r))
    (hf : VanishesOnRectanglesInDisc c r f) :
    ∀ᶠ (w : ℂ) in 𝓝 z,
      WedgeInt c w f - WedgeInt c z f = WedgeInt z w f := by
--%% \begin{proof}
  have hr : 0 < r := pos_of_mem_ball hz
--%% Set $r_1>0$ to be the distance from $z$ to the boundary of $D(c,r)$,
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simp only [mem_ball, gt_iff_lt] at hz ⊢; linarith
--%% so that the disc $D(z,r_1)$ is contained in $D(c,r)$.
  have z_ball : ball z r₁ ⊆ ball c r := ball_subset_ball₁ hz
--%% Then for $w$ to be in a ``neighborhood of $z$'', it suffices to be in $D(z,r_1)$.
  filter_upwards [ball_mem_nhds z r₁_pos]
  intro w w_in_z_ball
  have hzPlusH : w ∈ ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  simp only [WedgeInt]
--%% It is convenient to name some of the arising line integrals, to be used again and again.
--%% We define $I_1$ to be the integral along the horizontal path from $c$ to $\Re(w)+i\Im(c)$.
  set intI := ∫ x : ℝ in c.re..(w).re, f (x + c.im * I)
--%% We define $I_2$ to be the integral along the vertical path from $\Re(w)+i\Im(c)$ to $w$.
  set intII := I • ∫ y : ℝ in c.im..w.im, f (w.re + y * I)
--%% We define $I_3$ to be the integral along the horizontal path from $c$ to $\Re(z)+i\Im(c)$.
  set intIII := ∫ x : ℝ in c.re..z.re, f (x + c.im * I)
--%% We define $I_4$ to be the integral along the vertical path from $\Re(z)+i\Im(c)$ to $z$.
  set intIV := I • ∫ y : ℝ in c.im..z.im, f (z.re + y * I)
--%% We define $I_5$ to be the integral along the horizontal path from $z$ to $\Re(w)+i\Im(z)$.
  set intV := ∫ x : ℝ in z.re..w.re, f (x + z.im * I)
--%% We define $I_6$ to be the integral along the vertical path from $\Re(w)+i\Im(z)$ to $w$.
  set intVI := I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I)
--%% We define $I_7$ to be the integral along the horizontal path from $\Re(z)+i\Im(c)$ to
--%% $\Re(w)+i\Im(c)$.
  let intVII := ∫ x : ℝ in z.re..w.re, f (x + c.im * I)
--%% We define $I_8$ to be the integral along the vertical path from $\Re(w)+i\Im(c)$ to
--%% $\Re(w)+i\Im(z)$.
  let intVIII := I • ∫ y : ℝ in c.im..z.im, f (w.re + y * I)
  have integrableHoriz : ∀ a₁ a₂ b : ℝ, a₁ + b * I ∈ ball c r → a₂ + b * I ∈ ball c r
    → IntervalIntegrable (fun x => f (x + b * I)) MeasureTheory.volume a₁ a₂
  · intro a₁ a₂ b ha₁ ha₂
    apply ContinuousOn.intervalIntegrable
    convert ContinuousOn.comp (g := f) (f := fun (x : ℝ) => (x : ℂ) + b * I) (s := uIcc a₁ a₂)
      (t := (fun (x : ℝ) => (x : ℂ) + b * I) '' (uIcc a₁ a₂)) ?_ ?_ (mapsTo_image _ _)
    · apply f_cont.mono
      convert rectangle_in_convex (convex_ball c r) ha₁ ha₂ ?_ ?_ using 1 <;>
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add, ha₁, ha₂, Rectangle]
      simp only [le_refl, uIcc_of_le, Icc_self, horizontalSegment_eq a₁ a₂ b]
    · exact Continuous.continuousOn (Continuous.comp (continuous_add_right _) continuous_ofReal)
  have integrableVert : ∀ a b₁ b₂ : ℝ, a + b₁ * I ∈ ball c r → a + b₂ * I ∈ ball c r
    → IntervalIntegrable (fun y => f (a + y * I)) MeasureTheory.volume b₁ b₂
  · intro a b₁ b₂ hb₁ hb₂
    apply ContinuousOn.intervalIntegrable
    convert ContinuousOn.comp (g := f) (f := fun (y : ℝ) => (a : ℂ) + y * I) (s := uIcc b₁ b₂)
      (t := (fun (y : ℝ) => (a : ℂ) + y * I) '' (uIcc b₁ b₂)) ?_ ?_ (mapsTo_image _ _)
    · apply f_cont.mono
      convert rectangle_in_convex (convex_ball c r) hb₁ hb₂ ?_ ?_ using 1 <;>
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add, hb₁, hb₂, Rectangle]
      simp only [ le_refl, uIcc_of_le, Icc_self, verticalSegment_eq a b₁ b₂]
    · apply Continuous.continuousOn
      exact ((continuous_add_left _).comp (continuous_mul_right _)).comp continuous_ofReal
--%% Then $I_1$ is equal to $I_3+I_7$,
  have intIdecomp : intI = intIII + intVII
  · rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simp only [re_add_im, mem_ball, dist_self, hr]
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hzPlusH
--%% and $I_2$ is equal to $I_6+I_8$.
  have intIIdecomp : intII = intVIII + intVI
  · rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact cornerRectangle_in_disc hzPlusH
    · apply mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · apply mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · convert hzPlusH using 1; ext <;> simp
  have rectZero : intVIII = - intVII + intV + intIV
  · rw [← sub_eq_zero]
--%% Moreover, $I_7 - I_5 + I_8 - I_4$ forms a rectangle, and hence its integral is zero.
    have : intVII - intV + intVIII - intIV = 0 := by
      have wzInBall : w.re + ↑z.im * I ∈ ball c r :=
        by exact mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
      have wcInBall : w.re + c.im * I ∈ ball c r := by
        exact cornerRectangle_in_disc hzPlusH
      convert hf (z.re + c.im * I) (w.re + z.im * I) (cornerRectangle_in_disc hz) wzInBall
          (by simpa using hz) (by simpa using wcInBall) using 1
      rw [RectangleIntegral]
      congr <;> simp
    rw [← this]
    ring
  rw [intIdecomp, intIIdecomp, rectZero]
  ring
--%% Putting everything together shows that the wedge integral difference is equal to the wedge,
--%% as claimed.
--%% \end{proof}

/-%%
Next we claim that, as $x \to \Re(z)$, the horizontal integral of a continuous $f$
from $z$ to $x + i\Im(z)$ is equal to $(x - \Re(z)) f(z)$, up to $o(x - \Re(z))$.
\begin{lemma}
  \label{deriv_of_wedgeInt_re'}
  \lean{deriv_of_wedgeInt_re'}\leanok
  As $x \to \Re(z)$,
  $$
    \int_{\Re(z)}^x f(t + i\Im(z))\ dt
    =
    (x-\Re(z)) f(z)
    +
    o(x-\Re(z))
    .
  $$
\end{lemma}
%%-/
/-- The integral of a continuous function `f` from `z` to `x + z.im * I` is equal to
  `(x - z.re) * f z` up to `o(x - z.re)`. -/
theorem deriv_of_wedgeInt_re' {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun (x : ℝ) ↦ (∫ t in z.re..x, f (t + z.im * I))) =ᵤ (fun (x : ℝ) ↦ (x - z.re) * f z) upto o[𝓝 z.re]
    (fun (x : ℝ)  ↦ x - z.re) := by
--%% \begin{proof}
  suffices : (fun (x : ℝ) ↦ (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) * f z) =o[𝓝 z.re]
    (fun (x : ℝ)  ↦ x - z.re)
  · convert Asymptotics.EqUpToLittleO_apply.mpr this
  let r₁ := r - dist z c
  have : 0 < r₁ := by simp only [mem_ball, gt_iff_lt] at hz ⊢; linarith
  let s : Set ℝ := Ioo (z.re - r₁) (z.re + r₁)
  have zRe_mem_s : z.re ∈ s := by simp [mem_ball.mp hz]
  have s_open : IsOpen s := isOpen_Ioo
  have s_ball₁ : s ×ℂ {z.im} ⊆ ball z r₁
  · intro x hx
    obtain ⟨xRe, xIm⟩ := hx
    simp only [mem_preimage, mem_singleton_iff, mem_Ioo] at xRe xIm
    simp only [mem_ball]
    rw [dist_eq_re_im, xIm]
    simp only [sub_self, ne_eq, not_false_eq_true, zero_pow', add_zero, Real.sqrt_sq_eq_abs, abs_lt]
    refine ⟨by linarith, by linarith⟩
  have s_ball : s ×ℂ {z.im} ⊆ ball c r := Subset.trans s_ball₁ (ball_subset_ball₁ hz)
  have f_contOn : ContinuousOn (fun (x : ℝ) => f (x + z.im * I)) s
  · apply (hf.comp ((continuous_add_right _).comp continuous_ofReal).continuousOn)
    intro w hw
    change w + z.im * I ∈ ball c r
    apply s_ball
    rw [mem_reProdIm]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, gt_iff_lt, not_lt, ge_iff_le, mem_Ioo, add_im, mul_im, zero_add, mem_singleton_iff,
      and_true]
    apply hw
  have int1 : IntervalIntegrable (fun (x : ℝ) => f (x + z.im * I)) MeasureTheory.volume z.re z.re
  · apply ContinuousOn.intervalIntegrable
    apply f_contOn.mono
    simp [mem_ball.mp hz]
  have int2 : StronglyMeasurableAtFilter (fun (x : ℝ) => f (x + z.im * I)) (𝓝 z.re)
  · apply ContinuousOn.stronglyMeasurableAtFilter s_open f_contOn
    exact zRe_mem_s
  have int3 : ContinuousAt (fun (x : ℝ) => f (x + z.im * I)) z.re :=
    s_open.continuousOn_iff.mp f_contOn zRe_mem_s
--%% This is just the fundamental theorem of calculus.
  have := @intervalIntegral.integral_hasDerivAt_right (f := fun (x : ℝ) ↦ f (x + z.im * I)) (a := z.re) (b := z.re) _ _ _ int1 int2 int3
  dsimp [HasDerivAt, HasDerivAtFilter, HasFDerivAtFilter] at this
  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, map_sub] at this
  convert this using 3
  ring_nf
  congr
--%% \end{proof}

/-%%
Therefore as the complex varialbe $w \to z$, the horizontal integral of $f$ from $z$ to $\Re(w)+i\Im(z)$ is equal to $(\Re(w - z)) f(z)$, up to $o(w - z)$.
\begin{lemma}
  \label{deriv_of_wedgeInt_re}
  \lean{deriv_of_wedgeInt_re}\leanok
  As $w \to z$,
  $$
    \int_{\Re(z)}^{\Re(w)} f(t + i\Im(z))\ dt
    =
    (\Re(w-z)) f(z)
    +
    o(w-z)
    .
  $$
\end{lemma}
%%-/
/- The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z).re * f z` up to
  `o(w - z)`, as `w` tends to `z`. -/
theorem deriv_of_wedgeInt_re {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun (w : ℂ) ↦ (∫ x in z.re..w.re, f (x + z.im * I))) =ᵤ (fun (w : ℂ) ↦ (w - z).re * f z) upto o[𝓝 z]
    (fun (w : ℂ) ↦ w - z) := by
--%% \begin{proof}
  suffices : (fun (w : ℂ) ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - ((w - z).re) * f z) =o[𝓝 z]
    (fun w ↦ w - z)
  · convert Asymptotics.EqUpToLittleO_apply.mpr this
  have zReTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.re) (𝓝 z) (𝓝 z.re) :=
    by apply Continuous.tendsto Complex.continuous_re
  have := (deriv_of_wedgeInt_re' hf hz).comp_tendsto zReTendsTo
  have := this.trans_isBigO re_isBigO
--%% Simply apply the previous lemma, together with the fact that $\Re(w - z) = O(w - z)$ as $w \to z$.
  convert this using 2
  congr
  simp
--%% \end{proof}

/-%%
Similarly, as $y \to \Im(z)$, the vertical integral of $f$ from $z$ to $\Re(z)+iy$ is equal to $(y - \Im(z)) f(z)$, up to $o(y - \Im(z))$.
\begin{lemma}
  \label{deriv_of_wedgeInt_im'}
  \lean{deriv_of_wedgeInt_im'}\leanok
  As $y \to \Im(z)$,
  $$
    \int_{\Im(z)}^y f(\Re(z)+it)\ dt
    =
    (y-\Im(z)) f(z)
    +
    o(y-\Im(z))
    .
  $$
\end{lemma}
The proof is the same.
%%-/
theorem deriv_of_wedgeInt_im' {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun (y : ℝ) ↦ (∫ t in z.im..y, f (z.re + t * I))) =ᵤ (fun (y : ℝ ) ↦ (y - z.im) * f z) upto o[𝓝 z.im]
    fun y ↦ y - z.im := by
  suffices : (fun (y : ℝ) ↦ (∫ t in z.im..y, f (z.re + t * I)) - (y - z.im) * f z) =o[𝓝 z.im]
    fun y ↦ y - z.im
  · convert Asymptotics.EqUpToLittleO_apply.mpr this
  let r₁ := r - dist z c
  have : 0 < r₁ := by simp only [mem_ball, gt_iff_lt] at hz ⊢; linarith
  let s : Set ℝ := Ioo (z.im - r₁) (z.im + r₁)
  have zIm_mem_s : z.im ∈ s := by simp [mem_ball.mp hz]
  have s_open : IsOpen s := isOpen_Ioo
  have s_ball₁ : {z.re} ×ℂ s ⊆ ball z r₁
  · intro x hx
    obtain ⟨xRe, xIm⟩ := hx
    simp only [mem_preimage, mem_singleton_iff, mem_Ioo] at xRe xIm
    simp only [mem_ball]
    rw [dist_eq_re_im, xRe]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow', zero_add,
      sub_nonneg, Real.sqrt_sq_eq_abs, abs_lt, neg_sub]
    refine ⟨by linarith, by linarith⟩
  have s_ball : {z.re} ×ℂ s ⊆ ball c r := Subset.trans s_ball₁ (ball_subset_ball₁ hz)
  have f_contOn : ContinuousOn (fun (y : ℝ) => f (z.re + y * I)) s
  · apply hf.comp (((continuous_add_left _).comp (continuous_mul_right _)).comp continuous_ofReal).continuousOn
    intro w hw
    simp only [Function.comp_apply, mem_ball]
    apply s_ball
    rw [mem_reProdIm]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, mem_singleton_iff, add_im, mul_im, zero_add, gt_iff_lt, not_lt, ge_iff_le, mem_Ioo,
      true_and]
    apply hw
  have int1 : IntervalIntegrable (fun y => f (z.re + y * I)) MeasureTheory.volume z.im z.im
  · apply ContinuousOn.intervalIntegrable
    apply f_contOn.mono
    simp [mem_ball.mp hz]
  have int2 : StronglyMeasurableAtFilter (fun (y : ℝ) => f (z.re + y * I)) (𝓝 z.im)
  · apply ContinuousOn.stronglyMeasurableAtFilter s_open f_contOn
    exact zIm_mem_s
  have int3 : ContinuousAt (fun (y : ℝ) => f (z.re + y * I)) z.im :=
    s_open.continuousOn_iff.mp f_contOn zIm_mem_s
  have := @intervalIntegral.integral_hasDerivAt_right (f := fun (y : ℝ) ↦ f (z.re + y * I)) (a := z.im) (b := z.im) _ _ _ int1 int2 int3
  dsimp [HasDerivAt, HasDerivAtFilter, HasFDerivAtFilter] at this
  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, map_sub] at this
  convert this using 3
  ring_nf
  congr

theorem deriv_of_wedgeInt_im'' {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun w ↦ (∫ y in z.im..w.im, f (z.re + y * I)) - (w - z).im * f z)
    =o[𝓝 z] fun w ↦ w - z := by
  have zImTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.im) (𝓝 z) (𝓝 z.im) :=
    by apply Continuous.tendsto Complex.continuous_im
  have := (deriv_of_wedgeInt_im' hf hz).comp_tendsto zImTendsTo
  have := this.trans_isBigO im_isBigO
  convert this using 2
  congr
  simp

theorem deriv_of_wedgeInt_im''' {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ y in z.im..w.im, f (z.re + y * I)))
    =o[𝓝 z] fun w ↦ w - z := by

  sorry

theorem deriv_of_wedgeInt_im {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))
  {z : ℂ} (hz : z ∈ ball c r) :
  (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im * f z)
    =o[𝓝 z] fun w ↦ w - z :=
  calc
    _ = (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ y in z.im..w.im, f (z.re + y * I)))
        + (fun w ↦ (∫ y in z.im..w.im, f (z.re + y * I)) - (w - z).im * f z) :=
          by exact (sub_add_sub_cancel _ _ _).symm
    _ =o[𝓝 z] fun w => w - z := by
      convert (deriv_of_wedgeInt_im''' hf hz).add (deriv_of_wedgeInt_im'' hf hz) using 1

theorem deriv_of_wedgeInt {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (ball c r)) (hf : VanishesOnRectanglesInDisc c r f)
    {z : ℂ} (hz : z ∈ ball c r) :
    HasDerivAt (fun w => WedgeInt c w f) (f z) z := by
  have hr : 0 < r := pos_of_mem_ball hz
  dsimp [HasDerivAt, HasDerivAtFilter, HasFDerivAtFilter]
  calc
    _ =ᶠ[𝓝 z] (fun w ↦ WedgeInt z w f - (w - z) * f z) := ?_
    _ = (fun w ↦ (∫ x in z.re..w.re, f (↑x + ↑z.im * I)) - (w - z).re * f z)
        + I • (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im * f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z :=
      (deriv_of_wedgeInt_re f_cont hz).add ((deriv_of_wedgeInt_im f_cont hz).const_smul_left I)
  · filter_upwards [VanishesOnRectanglesInDisc.diff_of_wedges hz f_cont hf]
    exact fun a ha ↦ by rw [ha]
  ext1 w
  simp only [WedgeInt, smul_eq_mul, sub_re, ofReal_sub, sub_im, Pi.add_apply, Pi.smul_apply]
  set intI := ∫ (x : ℝ) in z.re..w.re, f (x + z.im * I)
  set intII := ∫ (y : ℝ) in z.im..w.im, f (w.re + y * I)
  calc
    _ = intI + I * intII - ((w - z).re + (w - z).im * I) * f z := by congr; rw [re_add_im]
    _ = intI + I * intII - ((w.re - z.re) + (w.im - z.im) * I) * f z := by simp
    _ = intI - (w.re - z.re) * f z + I * (intII - (w.im - z.im) * f z) := by ring

/-- Moreira's theorem
/-%%
This is Moreira's theorem.
\begin {theorem}[Moreira's theorem]
\label {moreira}
\lean {moreira}\leanok
Let $f$ be a continuous function on a disc $D(c,r)$, and suppose that $f$ vanishes on rectangles in $D(c,r)$. Then $f$ has a primitive on $D(c,r)$.
\end {theorem}
%%-/
-/
theorem moreiras_theorem {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (ball c r))
    (hf₂ : VanishesOnRectanglesInDisc c r f) :
    ∃ g : ℂ → ℂ, ∀ z ∈ (ball c r), HasDerivAt g (f z) z :=
  ⟨fun z ↦ WedgeInt c z f, fun _ hz ↦ deriv_of_wedgeInt hf hf₂ hz⟩

theorem vanishesOnRectangles_of_holomorphic {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : DifferentiableOn ℂ f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by
  convert integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ (by simp)
    ((hf.mono hU).continuousOn) ?_ using 1
  intro x hx
  apply hf.differentiableAt
  rw [mem_nhds_iff]
  refine ⟨Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im), ?_, ?_, ?_⟩
  · apply subset_trans ?_ hU
    rw [Rectangle]
    apply reProdIm_subset_iff'.mpr
    left
    constructor <;> convert uIoo_subset_uIcc _ _ using 1
  · exact IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  · convert hx using 1; simp

theorem vanishesOnRectanglesInDisc_of_holomorphic {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball c r)) :
    VanishesOnRectanglesInDisc c r f := fun z w hz hw hz' hw' ↦
  vanishesOnRectangles_of_holomorphic hf (rectangle_in_convex (convex_ball c r) hz hw hz' hw')

-- To prove the main theorem, we first prove it on a disc
theorem hasPrimitives_of_disc (c : ℂ) {r : ℝ} : HasPrimitives (ball c r) :=
  fun _ hf ↦ moreiras_theorem hf.continuousOn (vanishesOnRectanglesInDisc_of_holomorphic hf)

end Complex
