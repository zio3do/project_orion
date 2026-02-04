import Mathlib.Tactic

/-!
# Lean 4 Tactic Tutorial
A guided sampling of problems to give exposure to common tactics.

## Tactics Covered:
1. intro - Introduce hypotheses/variables
2. rfl - Reflexivity (prove things equal by definition)
3. rw - Rewrite using equalities
4. exact - Provide exact proof term
5. apply - Apply a theorem/hypothesis
6. cases - Case analysis/pattern matching
7. induction - Proof by induction
8. simp - Simplify using simp lemmas
-/

/-! ## 1. INTRO TACTIC
The `intro` tactic introduces variables and hypotheses into the context.
Think of it as "assuming" or "let's say" in mathematical prose.
-/

-- Example 1a: Basic intro
example (p q : Prop) : p → q → p := by
/-
Think of → as "function arrow":

p → q → p is a function that takes p and q as inputs, returns p
intro accepts the inputs (introduces parameters)
exact returns the output (provides the result)

in this case, we need to introduce a proof of q specifically because of the dependence q → p.
we cannot simply bypass the q → p and return p directly because of how we have defined the function.
-/
  intro hp hq       -- Assume we have a proof of p, call it hp; Assume we have a proof of q, call it hq
  exact hp        -- Return hp (the proof is EXACTLY hp, which is what we need)

-- Example 1b: Multiple intros at once
example (p q r : Prop) : p → q → r → p := by
  intro hp hq hr  -- Introduce all three hypotheses at once
  exact hp        -- We just need to return p

-- Example 1c: Intro with functions
example : ∀ n : Nat, n + 0 = n := by
  intro n         -- Let n be an arbitrary natural number
  rw [add_comm, Nat.zero_add] -- rewrote


/-! ## 2. RFL TACTIC
The `rfl` (reflexivity) tactic proves that two things are equal when they are
definitionally equal - i.e., they're the same after unfolding definitions.
-/

-- Example 2a: Simple reflexivity
example : 2 + 2 = 4 := by
/-
Difference between this example and the Natural Number Game: definitional equality vs propositional equality.

Definitional: 2 is notation for Nat.succ (Nat.succ 0). Addition on Nat is defined recursively. Thus, Lean can unfold the definition and we can invoke rfl immediately.

Propositional: example (n : Nat) : n + 0 = n := by
  -- rfl  -- This would FAIL!
  exact Nat.add_zero n  -- Need the theorem because n + 0 is not definitionally equal to n for arbitrary n.
-/
  rfl             -- Lean computes 2 + 2 and sees it equals 4

-- Example 2b: Reflexivity with variables
example (n : Nat) : n = n := by
  rfl             -- Anything equals itself

-- Example 2c: Definitional equality
example : (fun x => x + 1) 5 = 6 := by
 -- fun is lambda function syntax in Lean
  rfl             -- (fun x => x + 1) 5 evaluates to 5 + 1 = 6

-- Example 2d: List concatenation
example : [1, 2] ++ [3, 4] = [1, 2, 3, 4] := by
  rfl             -- List concatenation is computed


/-! ## 3. RW TACTIC
The `rw` (rewrite) tactic replaces part of the goal using an equality.
Format: `rw [theorem_name]` or `rw [← theorem_name]` (backwards)
-/

-- Example 3a: Basic rewrite
example (a b c : Nat) (h : a = b) : a + c = b + c := by
-- i think rw has an automatic rfl step built in at the end
  rw [h]          -- Replace a with b using hypothesis h
  -- Goal is now: b + c = b + c

-- Example 3b: Multiple rewrites
example (x y : Nat) : x + 0 + (y + 0) = x + y := by
  rw [Nat.add_zero]  -- Rewrite first occurrence: x + 0 → x
  rw [Nat.add_zero]  -- Rewrite second occurrence: y + 0 → y
  -- Alternatively: repeat rw[Nat.add_zero]
  -- Goal is now: x + y = x + y

-- Example 3c: Backward rewrite (←)
example (a b : Nat) (h : a = b + 1) : b + 1 = a := by
  rw [← h]        -- Rewrite backwards: a → b + 1
  -- Goal becomes: b + 1 = b + 1

-- Example 3d: Rewrite in hypothesis
example (a b c : Nat) (h1 : a = b) (h2 : a = c) : b = c := by
  rw [h1] at h2 -- Rewrite h2 using h1: a = c becomes b = c
  exact h2        -- Now h2 is exactly what we need


/-! ## 4. EXACT TACTIC
The `exact` tactic provides the exact proof term needed for the goal.
Use it when you have exactly what you need in the context.
-/

-- Example 4a: Using a hypothesis
example (p q : Prop) (hp : p) (hq : q) : p := by
  exact hp        -- hp is exactly a proof of p

-- Example 4b: Exact with simple computation
example : 7 = 7 := by
  exact rfl       -- rfl is a proof of equality. didn't have to use exact here, but we can.

-- Example 4c: Constructing a proof term
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩  -- Construct proof of conjunction using ⟨_, _⟩

-- Example 4d: Using a theorem
example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n  -- Apply the theorem directly


/-! ## 5. APPLY TACTIC
The `apply` tactic applies a theorem or hypothesis to transform the goal.
If theorem proves A → B and goal is B, `apply` changes goal to A.
-/

-- Example 5a: Basic apply
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  apply h2        -- Goal r becomes q (since h2 : q → r)
  apply h1        -- Goal q becomes p (since h1 : p → q)
  exact hp        -- We have p

-- Example 5b: Apply with multiple arguments
example (a b c : Nat) (h : a = b → b = c → a = c) (hab : a = b) (hbc : b = c) : a = c := by
  apply h         -- Need to prove a = b and b = c
  · exact hab     -- First goal: a = b
  · exact hbc     -- Second goal: b = c

-- Example 5c: Apply a theorem
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  repeat rw[← Nat.succ_eq_add_one]  -- Rewrite both sides to be a direct function of n,m resp
  apply congrArg -- Apply congruence: if n = m, then f n = f m
  exact h

-- Example 5d: Apply with Nat.le
example (n : Nat) : n ≤ n + 1 := by
  apply Nat.le_succ  -- Applies theorem: n ≤ n.succ


/-! ## 6. CASES TACTIC
The `cases` tactic performs case analysis on a hypothesis or expression.
Use it to break down disjunctions (∨), existentials (∃), or data constructors.
-/

-- Example 6a: Cases on disjunction
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp =>
    apply Or.inr  -- Prove q ∨ p by proving p
    exact hp
  | inr hq =>
    apply Or.inl -- Prove q ∨ p by proving left side: q
    exact hq


-- Example 6b: Cases on conjunction
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  cases h with
  | intro hp hq =>  -- Break h into hp : p and hq : q
    constructor     -- Split goal into two: q and p
    · exact hq      -- Prove q
    · exact hp      -- Prove p

-- Example 6c: Cases on natural numbers
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero =>       -- prove the n = 0 case
    apply Or.inl  -- we just want to prove LHS of or statement
    rfl           -- 0 = 0
  | succ k =>     -- as infoView suggested, need to prove succ case where n = k+1
    apply Or.inr  -- just proving RHS of equation
    simp          -- simplify k+1 and realize that it is bigger than 0


-- Example 6d: Cases with existential
example (p : Nat → Prop) (h : ∃ n, p n) : ∃ m, p m := by
 -- problem statement is basically saying "if there exists an n such that p n holds, then there exists an m such that p m holds"
 cases h with
 | intro n hn
 exact ⟨n, hn⟩ -- “I choose m := n, and here is the proof that p m holds.”



/-! ## 7. INDUCTION TACTIC
The `induction` tactic proves statements by mathematical induction.
Essential for proving properties about natural numbers and recursive structures.
-/

-- Example 7a: Basic induction on Nat
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- Base case: prove 0 + 0 = 0
    rfl
  | succ k ih =>
    -- Inductive step: assume 0 + k = k (this is ih)
    -- Prove: 0 + (k + 1) = k + 1
    rw [Nat.add_succ]  -- 0 + (k + 1) = (0 + k) + 1
    rw [ih]            -- Use inductive hypothesis: 0 + k = k

-- Example 7b: Induction with addition
example (n m : Nat) : n + m = m + n := by
  induction m with
  | zero =>
    -- Base: n + 0 = 0 + n
    rw [Nat.add_zero, Nat.zero_add]
  | succ k ih =>
    -- Inductive: assume n + k = k + n, prove n + (k+1) = (k+1) + n
    rw [Nat.add_succ, Nat.succ_add]  -- Convert to successor form
    rw [ih]                          -- Apply inductive hypothesis


/-! ## 8. SIMP TACTIC
The `simp` tactic automatically simplifies the goal using a database of lemmas.
It's powerful but can be unpredictable - use it when the simplification is obvious.
-/

-- Example 8a: Basic simplification
example (n : Nat) : n + 0 + 0 = n := by
  simp  -- Automatically applies Nat.add_zero twice

-- Example 8b: Simplify with lists
example (xs ys : List Nat) : xs ++ [] ++ ys = xs ++ ys := by
  simp  -- Simplifies list operations

-- Example 8c: Simp with specific lemmas
example (a b : Nat) : a + b + 0 = b + a := by
  simp only [Nat.add_zero, Nat.add_comm]  -- Only use these lemmas

-- Example 8d: Simp in hypothesis
example (n m : Nat) (h : n + 0 = m + 0) : n = m := by
  simp at h  -- Simplify the hypothesis first
  exact h    -- Now h : n = m

-- Example 8e: Arithmetic simplification
example (a b c : Nat) : a + (b + c) = (a + b) + c := by
  simp [Nat.add_assoc]  -- Simp with associativity


/-! ## PRACTICE PROBLEMS
-/

-- Practice 1: Use intro and exact
example (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by
/-
So q and r are "covered". p implies q, and q implies r.
The reason we need intro hp is because we need to assume something implies p. That is, assume the premise p of an implication to
-/
  intro hp -- the goal shifts from p → r to r
  apply h2 -- the goal shifts from r to q
  apply h1 -- the goal shifts from q to p
  exact hp -- we already assumed p with intro hp

-- Practice 2: Use rw and rfl
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw[h2]


-- Practice 3: Use cases
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq =>
  apply Or.inl
  exact hq
  | inl hp =>
  apply Or.inr
  exact hp

-- Practice 4: Use induction
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
  simp
  | succ hd =>
  rw[Nat.add_zero]

-- Practice 5: Combine tactics
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  -- can just use rw
  rw[h]
