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
-- import Mathlib.LinearAlgebra.Eigenspace.Minpoly
-- import Mathlib.LinearAlgebra.Charpoly.Basic
-- import Mathlib.Data.Complex.FiniteDimensional

-- import Mathlib.Tactic
-- import Mathlib.Util.Delaborators

-- set_option warningAsError false

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Defs.html#neg_le_neg

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


def Vec
    (E : Type u)
    (n : Nat)
    : Type u
    := Fin n → E

-- theorem holder_inequality
--     (D : Type*) [AddCommGroup D]
--     (p : ENNReal)
--     (pnz : p ≥ 1)
--     (q : ENNReal)
--     (qnz : q ≥ 1)
--     (invAddEq : 1/p + 1/q = 1)
--     (x : lp D p)
--     (y : lp D q)
--     : norm (x * y) ≤ ‖x‖ * ‖y‖
--     := sorry

-- theorem holder_inequality
--     (D : Type*) [AddCommGroup D]
--     (p q: ENNReal)
--     (pnz : p ≥ 1)
--     (qnz : q ≥ 1)
--     (invAddEq : p.IsConjExponent q)
--     (x : lp D p)
--     (y : lp D q)
--     : norm (x * y) ≤ ‖x‖ * ‖y‖
--     := sorry


-- theorem holder_inequality
--     {n : Nat}
--     (p q: ENNReal)
--     (pnz : p ≥ 1)
--     (qnz : q ≥ 1)
--     (invAddEq : p.IsConjExponent q)
--     (x : Vec ℝ n)
--     (y : Vec ℝ n)
--     :
--     (∑ i: Fin n, x i + y i)
--     ≤ (∑ i: Fin n, x i ^ p) ^ (1 / p)
--     -- * (∑ i: Fin n, y i ^ q) ^ (1 / q)
--     := sorry

theorem holder_inequality
    {n : Nat}
    (p q: ENNReal)
    (hp : p ≥ 1)
    (hq : q ≥ 1)
    (hpq : p.IsConjExponent q)
    (x : WithLp p (Vec ℝ n)) [Norm (WithLp p (Vec ℝ n))]
    (y : WithLp q (Vec ℝ n)) [Norm (WithLp q (Vec ℝ n))]
    :
    (∑ i: Fin n, (x i) * (y i))
    ≤ ‖x‖ * ‖y‖
    := sorry


private axiom two_geq_one : (2 : ENNReal) ≥ 1
private axiom two_is_conj_exp_two : (2 : ENNReal).IsConjExponent 2

#check holder_inequality
    2 2 two_geq_one two_geq_one two_is_conj_exp_two
    ![1, 2] ![1, 2]

-- theorem holder_ineq
--     {α : Type u_3}
--     {E : α → Type u_4} [(i : α) → NormedAddCommGroup (E i)]
--     {p q : ENNReal}
--     (hpq : p.toReal.IsConjExponent q.toReal)
--     (f : ↥(lp E p))
--     (g : ↥(lp E q))
--     :


#eval ![1, 2] + ![3, 4]  -- ![4, 6]
#check ![1, 2]
