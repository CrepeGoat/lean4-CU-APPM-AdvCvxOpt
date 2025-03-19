import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Init.Prelude
import Mathlib.Data.Matrix.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Real.ConjExponents
import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

Math implementation for lecture 00:
https://github.com/stephenbeckr/convex-optimization-class/blob/main/Notes/00_IntroToOptProblems.pdf

uses CvxLean as a reference:
- https://github.com/verified-optimization/CvxLean/blob/c62c2f292c6420f31a12e738ebebdfed50f6f840/CvxLean/Lib/Minimization.lean

-/


/-- min of f(x) for all x in C -/
def MinimumOn
    {Domain: Type*}
    {Range: Type*} [LE Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    (value : Range)
    : Prop
    := Minimal (fun y : Range => y ∈ ConstraintSet.image objective) value

/-- max of f(x) for all x in C -/
def MaximumOn
    {Domain: Type*}
    {Range: Type*} [LE Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    (value : Range)
    : Prop
    := Maximal (fun y : Range => y ∈ ConstraintSet.image objective) value

/- Remark -/
/--
Convert a min expression to a max via the equation:

min_x f(x) = -max_x (-f(x))
-/
def min_obj_to_neg_max_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    {min : R}
    (hmin: MinimumOn f C min)
    : MaximumOn (fun x: D => -(f x)) C (-min)
    := by
        constructor
        case left => simp; exact hmin.left
        have hr := hmin.right
        simp; simp at hr
        exact hr

/--
Convert a max expression to a min via the equation:

max_x f(x) = -min_x (-f(x))
-/
def max_obj_to_neg_min_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    {min : R}
    (hmin: MaximumOn f C min)
    : MinimumOn (fun x: D => -(f x)) C (-min)
    := by
        constructor
        case left => simp; exact hmin.left
        have hr := hmin.right
        simp; simp at hr
        exact hr

/-- y s.t. f(y) = min of f(x) for all x in C -/
def ArgumentMinimumOn
    {Domain: Type*}
    {Range: Type*}  [LE Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    : Set Domain
    := setOf fun xmin: Domain =>
        xmin ∈ ConstraintSet
        ∧ ∀ x ∈ ConstraintSet, objective xmin ≤ objective x

/-- inf of f(x) for all x in C -/
def InfimumOn
    {Domain: Type*}
    {Range: Type*} [LE Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    (value : Range)
    : Prop
    := Maximal (fun y: Range => ∀ x ∈ ConstraintSet, y ≤ objective x) value

/-- sup of f(x) for all x in C -/
def SupremumOn
    {Domain: Type*}
    {Range: Type*} [LE Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    (value : Range)
    : Prop
    := Minimal (fun y: Range => ∀ x ∈ ConstraintSet, objective x ≤ y) value

/- Remark -/
/--
Convert an inf expression to a sup via the equation:

inf_x f(x) = -sup_x (-f(x))
-/
def inf_obj_to_neg_sup_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    {inf: R}
    (hinf: InfimumOn f C inf)
    : SupremumOn (fun x: D => -(f x)) C (-inf)
    := by
        constructor
        case left => simp; exact hinf.left
        case right =>
            intro y hNegObjLeY h
            have hYLeNegObj := fun x : D => fun hXInC : x ∈ C =>
                hNegObjLeY x hXInC |> neg_le.mp
            exact hinf.right hYLeNegObj (le_neg.mp h) |> neg_le.mp

/--
Convert a sup expression to an inf via the equation:

sup_x f(x) = -inf_x (-f(x))
-/
def sup_obj_to_neg_inf_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    {sup: R}
    (hsup: SupremumOn f C sup)
    : InfimumOn (fun x: D => -(f x)) C (-sup)
    := by
        constructor
        case left => simp; exact hsup.left
        case right =>
            intro y hYLeNegObj h
            have hObjLeNegY := fun x : D => fun hXInC : x ∈ C =>
                hYLeNegObj x hXInC |> le_neg.mp
            exact hsup.right hObjLeNegY (neg_le.mp h) |> le_neg.mp


/--
If a function is L-continuous, any two points that are a distance `d` apart
are no more than `L * d` apart when mapped through the function.
-/
def lipschitz_continuous
    [Field ℝ] [Lattice ℝ]
    {ℝn : Type*} [NormedAddCommGroup ℝn] [NormedSpace ℝ ℝn]
    (f : ℝn → ℝ)
    (L : NNReal)
    : Prop
    := ∀ x y : ℝn, abs ((f y) - (f x)) ≤ L * dist y x

#check lipschitz_continuous (fun x => ![1, 3] ⬝ᵥ x) (3 : NNReal)


theorem holder_inequality
    {n : Nat}
    (p q: ENNReal)
    (hp : p ≥ 1)
    (hq : q ≥ 1)
    (hpq : p.IsConjExponent q)
    (x : WithLp p (Fin n → ℝ)) [Norm (WithLp p (Fin n → ℝ))]
    (y : WithLp q (Fin n → ℝ)) [Norm (WithLp q (Fin n → ℝ))]
    :
    (∑ i: Fin n, (x i) * (y i))
    ≤ ‖x‖ * ‖y‖
    := sorry


def epsilon_optimal
    {D: Type*}
    {R: Type*} [LE R] [HSub R R R]
    (obj: D → R)
    (C: Set D)
    (min : R)
    (hmin : MinimumOn obj C min)
    (value : D)
    (epsilon : R)
    : Prop
    := obj value - min ≤ epsilon
