/-
This file defines and proves the equisatisfiability of the direct (or naive)
encoding for the n-variable XOR gate.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import xor.xor
import basic

import data.list.basic
import data.nat.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

namespace xor_gate

open literal
open clause
open cnf
open list
open xor_gate
open explode
open nat

/-! # Direct encoding -/
section direct_encoding

variables {g : xor_gate V} {c : clause V}

/- The direct encoding is the set of all possible clauses with an even number 
   of negations on the provided literals in a single CNF formula. -/
def direct_xor : xor_gate V → cnf V
| []        := [[]]
| (l :: ls) := (explode (map var ls)).map 
      (λ c, cond (bodd (c.count_flips (ls)) = ff) (l :: c) (l.flip :: c))

@[simp] theorem direct_xor_nil : direct_xor ([] : xor_gate V) = [[]] := rfl

@[simp] theorem direct_xor_singleton (l : literal V) : direct_xor [l] = [[l]] :=
by simp [direct_xor]

theorem mem_explode_of_mem_direct_xor : 
  c ∈ direct_xor g → c ∈ explode (map var g) :=
begin
  cases g with l ls,
  { simp only [explode_nil, imp_self, direct_xor_nil, map_nil] },
  { simp [direct_xor, explode],
    intros cl hcl,
    cases l,
    { cases (bodd (cl.count_flips ls)),
      { simp, intro h, use [cl, hcl, h] },
      { simp, intro h, unfold literal.flip at h, 
        right, use [cl, hcl, h] } },
    { cases (bodd (cl.count_flips ls)),
      { simp, intro h, right, use [cl, hcl, h] },
      { simp, intro h, unfold literal.flip at h,
        use [cl, hcl, h] } } }
end

theorem length_direct_xor : g ≠ [] → length (direct_xor g) = 2^(length g - 1) :=
begin
  cases g,
  { contradiction },
  { simp only [direct_xor, length_explode, add_zero, length, add_succ_sub_one, 
      ne.def, forall_true_left, not_false_iff, length_map] }
end

theorem length_direct_xor_pos : g ≠ [] → length (direct_xor g) > 0 :=
assume h, by simp only [length_direct_xor h, succ_pos', gt_iff_lt, pow_pos]

theorem exists_mem_direct_xor (g : xor_gate V) : 
  ∃ (c : clause V), c ∈ direct_xor g :=
begin
  cases g with l ls,
  { use [nil, mem_singleton_self nil] },
  { exact exists_mem_of_length_pos (length_direct_xor_pos (cons_ne_nil l ls)) }
end

-- These theorems begin to be dependent on order of encoding
-- If the underlying type of xor_gate changes to (fin)set, must update
theorem map_var_eq_of_mem_direct_xor :
  c ∈ direct_xor g → map var c = map var g :=
begin
  cases g with l ls,
  { simp only [direct_xor, imp_self, map_eq_nil, map_nil, mem_singleton] },
  { simp [direct_xor],
    intros c hc,
    cases (bodd (c.count_flips ls)),
    { simp only [if_true, eq_self_iff_true],
      rintro rfl,
      simp [map_var_eq_iff_mem_explode.mpr hc] },
    { simp only [if_false],
      rintro rfl,
      simp [map_var_eq_iff_mem_explode.mpr hc, flip_var_eq] } }
end

theorem even_flips_iff_mem_direct_xor_of_map_var_eq : map var c = map var g → 
  (bodd (c.count_flips g) = ff ↔ c ∈ direct_xor g) :=
begin
  intro hc, split,
  { cases g with l ls,
    { revert hc, simp },
    { simp only [direct_xor, map_cons, bool.cond_to_bool, mem_map],
      intro hf,
      rcases exists_cons_of_map_cons hc with ⟨x, xs, rfl, hx, hxs⟩,
      use xs, split,
      { exact map_var_eq_iff_mem_explode.mp hxs },
      { cases h : (bodd (clause.count_flips xs ls)),
        { rcases var_eq_iff_eq_or_flip_eq.mp hx with rfl | hx,
          { simp only [if_true, eq_self_iff_true] },
          { simp [clause.count_flips, hx] at hf,
            rw h at hf, contradiction } },
        { rcases var_eq_iff_eq_or_flip_eq.mp hx with hx | rfl,
          { simp [clause.count_flips, hx] at hf,
            rw h at hf, contradiction },
          { simp only [flip_flip, if_false] } } } } },
  { cases g with l ls,
    { simp },
    { simp only [direct_xor, bool.cond_to_bool, mem_map],
      rintro ⟨a, ha, hf⟩,
      rcases exists_cons_of_map_cons hc with ⟨x, xs, rfl, hx, hxs⟩,
      cases h : (nat.bodd (a.count_flips ls));
      { simp only [h, if_true, eq_self_iff_true, if_false] at hf,
        simp [← hf, clause.count_flips, literal.is_neg, 
          bool.to_nat, h, flip_flip _, flip_ne] } } }      
end

theorem odd_flips_iff_not_mem_direct_xor_of_map_var_eq : map var c = map var g → 
  (bodd (c.count_flips g) = tt ↔ c ∉ direct_xor g) :=
begin
  intro hc, split,
  { intro hcount, by_contradiction,
    rw (even_flips_iff_mem_direct_xor_of_map_var_eq hc).mpr h at hcount,
    contradiction },
  { contrapose, simp only [eq_ff_eq_not_eq_tt, not_not],
    exact (even_flips_iff_mem_direct_xor_of_map_var_eq hc).mp }
end

theorem direct_xor_equisatisfiable (g : xor_gate V) :
  assignment.eqsat (λ α, cnf.eval α (direct_xor g)) (λ α, g.eval α) :=
begin
  split,
  { rintros ⟨α, ha⟩,
    use α, simp [eval_eq_bodd_count_tt α g], simp at ha,
    rcases exists_mem_direct_xor g with ⟨c, hc⟩,
    by_contradiction,
    rw eq_ff_eq_not_eq_tt at h,
    --rw clause.count_tt_pos_eq_count_neg_falsify at h,
    --have := eval_tt_iff_forall_clause_eval_tt.mp ha,
    rw [← clause.count_flips_falsify_eq_count_tt, count_flips_comm] at h,
    have falsify_mem := mem_direct_xor_of_even_flips_of_map_var_eq
      (map_var_falsify_eq_list α (map var l)) h,
  have falsify_eval := falsify_eval_ff α (map var l),
  have := this (falsify α (map var l)) falsify_mem,
  exact absurd_bool this falsify_eval
  },
  { rintros ⟨α, ha⟩,
    rw xor_odd_eval_tt α g at ha,
  rw ← gate_eq_clause l at ha,
  use α,
  apply eval_tt_iff_forall_clause_eval_tt.mpr,
  intros c hc,
  have mve := map_var_eq_of_mem_direct_xor hc,
  have neqodd := neq_of_ff_of_tt ha ((even_flips_iff_mem_direct_xor mve).mpr hc),
  have neq := ne_of_apply_ne nat.bodd neqodd,
  rw count_flips_comm at neq,
  exact eval_tt_of_neq_flips mve.symm neq

    exact exists_xor_of_direct_xor ⟨α, ha⟩ }
end

-- Some proofs require that the naive encoding exactly represents xor. Equality is stronger
-- Technically, equality is stronger than equisatisfiability, think about replacing above?
theorem eval_direct_xor_eq_eval_xor_gate (l : list (literal V)) (α : assignment V) :
  cnf.eval α (direct_xor l) = xor_gate.eval α l :=
begin
  cases l with l ls,
  { simp },
  { have red := xor_odd_eval_tt2 α (l :: ls),
    cases h : (xor_gate.eval α (l :: ls));
    rw [h, ← gate_eq_clause (l :: ls)] at red,
    { apply eval_ff_iff_exists_clause_eval_ff.mpr,
      use (falsify α (map var (l :: ls))),
      split,
      { rw ← count_flips_falsify_eq_count_tt α (l :: ls) at red,
        rw count_flips_comm at red,
        apply (even_flips_iff_mem_direct_xor (map_var_falsify_eq_list α (map var (l :: ls)))).mp,
        exact red.symm },
      { exact falsify_eval_ff α (map var (l :: ls)) } },
    { apply eval_tt_iff_forall_clause_eval_tt.mpr,
      intros c hc,
      have mve := map_var_eq_of_mem_direct_xor hc,
      have neqodd := neq_of_ff_of_tt (eq.symm red) ((even_flips_iff_mem_direct_xor mve).mpr hc),
      have neq := ne_of_apply_ne nat.bodd neqodd,
      rw count_flips_comm at neq,
      exact eval_tt_of_neq_flips mve.symm neq }
  }
end

theorem vars_cnf_subset_xor {ls : list (literal V)} :
  ls ≠ [] → cnf.vars (direct_xor ls) ⊆ (map var ls) :=
begin
  intro h,
  cases ls,
  { contradiction },
  { intros n hn,
    rcases cnf.exists_mem_clause_of_mem_vars hn with ⟨c, hcnf, hc⟩,
    simp [← map_var_eq_of_mem_direct_xor hcnf, mem_vars_iff_mem_map_vars, hc] }
end

theorem vars_direct_xor_subset_vars {l : list (literal V)} :
  l ≠ [] → cnf.vars (direct_xor l) ⊆ clause.vars l :=
assume h, subset.trans (vars_cnf_subset_xor h) (map_var_subset_of_vars l)

end direct_encoding

end xor_gate
