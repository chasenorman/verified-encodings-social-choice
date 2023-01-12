import cnf.literal
import cnf.assignment
import cnf.cnf
import cnf.encoding

import cardinality.direct_amo
import cardinality.sinz_amo
import cardinality.distinct
import cardinality.alk
import cardinality.amk

import data.nat.basic
import data.list.basic
import data.list.range

--import algebra.order.monoid.nat_cast
import logic.equiv.fin

open nat
open list
open function
open literal
open encoding
open clause cnf
open assignment
open alk amk distinct
open direct_amo
open sinz_amo

@[derive decidable_eq]
structure graph := (n : ℕ) (p : 0 < n) (w : fin n → fin n → ℤ) --(a : anti_symmetric w)

@[derive decidable_eq]
structure pointed_graph := (g : graph) (v : fin g.n)

instance pointed_graph_inhabited : inhabited pointed_graph := 
  inhabited.mk ⟨⟨1, nat.zero_lt_one, λ x y, 0⟩ , 0⟩

--  inhabited.mk ⟨⟨bool, bool.fintype, inhabited.mk ff, bool.decidable_eq, λ x y, 0⟩, ff⟩

structure graph_embedding := (g₁ : graph) (g₂ : graph) (f : fin g₁.n → fin g₂.n) (x : fin g₂.n) (p : set.univ \ (set.range f) = {x})

def simple {V : Type} (a b : V) : fin 2 → V := (fin_two_arrow_equiv V).inv_fun ⟨a, b⟩

def special1 (e : graph_embedding) (v : fin e.g₁.n) : graph := 
  ⟨2, zero_lt_two, 
    (ite (e.g₂.w (e.f v) e.x > 0) 
      (λ a b, e.g₂.w (simple (e.f v) e.x a) (simple (e.f v) e.x b))
      (λ a b, e.g₂.w (simple (e.f v) e.x b) (simple (e.f v) e.x a)))⟩

def special2 (e : graph_embedding) (v : fin e.g₁.n) : fin 2 := 
  (ite (e.g₂.w (e.f v) e.x > 0) ⟨0, zero_lt_two⟩ ⟨1, one_lt_two⟩)

def encoding (D : list graph) (E : list graph_embedding) : cnf pointed_graph := 
  -- at least one literal selected for each graph
  (D.map (λ g: graph, list.of_fn (λ v, Pos ⟨g, v⟩))) ++ 
  -- at most one literal selected for each graph
  join (D.map (λ g: graph, direct_amo (list.of_fn (λ v, Pos ⟨g, v⟩)))) ++
  -- binary gamma for each embedding
  join (E.map (λ e, (list.of_fn (λ v, [Neg ⟨special1 e v, special2 e v⟩, Neg ⟨e.g₁, v⟩, Pos ⟨e.g₂, e.f v⟩])) ))

#eval (encoding [⟨1, nat.zero_lt_one, λ x y, 0⟩] nil)

def binary_gamma (E : list graph_embedding) (f : Π g : graph, fin g.n) := ∀ e : graph_embedding, e ∈ E → (f (special1 e (f e.g₁))) = (special2 e (f e.g₁)) → (f e.g₂ = e.f (f e.g₁))

lemma lemma1 {n : ℕ} (a : ¬ n = 1) (b : ¬ n ≥ 2) : n = 0 := by omega

theorem encodes_binary_gamma : ∀ D E f, binary_gamma E f → (((encoding D E).eval (λ ⟨g, v⟩, f g = v)) = tt) := 
begin
  intros D E f bg,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  simp [encoding] at hcl,
  rcases hcl with (⟨g, gd, h⟩ | ⟨g, gd, hcl⟩ | ⟨e, ee, h⟩),
  {
    subst h,
    simp [eval_tt_iff_exists_literal_eval_tt, list.mem_of_fn],
    use f g,
    simp [literal.eval],
  },
  {
    by_cases (length (list.of_fn (λ v, Pos (pointed_graph.mk g v)))) ≥ 2,
    {
      rcases exists_double_flip_eq_of_mem h hcl with ⟨lit₁, lit₂, rfl⟩,
      rcases distinct_iff_mem.mpr hcl with ⟨i, j, hi, hj, hij, rfl, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      simp [eval_flip, literal.flip],
      by_contradiction,
      simp [literal.eval] at h,
      cases h with h1 h2,
      rw h1 at h2,
      exact (eq.not_lt (fin.veq_of_eq h2)) hij,
    },
    let h2 := h,
    by_cases (length (list.of_fn (λ v, Pos (pointed_graph.mk g v)))) = 1,
    {
      rw list.length_eq_one at h,
      cases h with a h,
      rw h at hcl,
      rw direct_amo_singleton at hcl,
      exfalso,
      exact list.not_mem_nil cl hcl,
    },
    let h3 := lemma1 h h2,
    {
      rw list.length_eq_zero at h3,
      rw h3 at hcl,
      rw direct_amo_nil at hcl,
      exfalso,
      exact list.not_mem_nil cl hcl,
    },
  },
  {
    rw list.mem_of_fn at h,
    rw set.mem_range at h,
    cases h with y h,
    subst h,
    simp [eval_tt_iff_exists_literal_eval_tt],
    simp [literal.eval],
    
    apply not_or_of_imp,
    intro sp,
    apply not_or_of_imp,
    intro veq,

    unfold binary_gamma at bg,
    specialize bg e ee,
    rw <-veq at sp,
    specialize bg sp,
    rw <-veq,
    exact bg,
  }
end