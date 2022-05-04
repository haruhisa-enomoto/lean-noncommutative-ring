import ring_theory.finiteness

universes u v

variables {R : Type u} [ring R]
variables {M : Type v} [add_comm_monoid M] [module R M]

variables (R) (M)

def ring.radical : ideal R := Inf { I : ideal R | I.is_maximal }

namespace submodule

def module.radical : submodule R M := Inf { N : submodule R M | is_coatom N }

lemma finite_span_is_compact_element (S : finset M) :
  complete_lattice.is_compact_element (span R S : submodule R M) :=
begin
  rw span_eq_supr_of_singleton_spans,
  simp only [finset.mem_coe],
  rw ←finset.sup_eq_supr,
  exact complete_lattice.finset_sup_compact_of_compact S
    (λ x _, singleton_span_is_compact_element x),
end

variables {R} {M}

lemma is_coatomic_of_module_finite (h : module.finite R M) : is_coatomic (submodule R M) :=
begin
  apply complete_lattice.coatomic_of_top_compact,
  rw module.finite_def at h,
  obtain ⟨S, hS⟩ := h,
  exact hS ▸ finite_span_is_compact_element R M S,
end

/--
Every proper submodule of a finitely generated module is contained in some maximal submodule.
-/
theorem exists_le_maximal (h : module.finite R M) (N : submodule R M) (hN : N ≠ ⊤) :
  ∃ L : submodule R M, (is_coatom L) ∧ N ≤ L :=
begin
  haveI := is_coatomic_of_module_finite h,
  exact (eq_top_or_exists_le_coatom N).resolve_left hN,
end

/--
One version of noncommutative Nakayama.
$N + rad M = M$ for a finitely generated module $M$ implies $N = M$.
-/
theorem eq_top_of_self_add_module_radical_eq_top
  (N : submodule R M) (h : module.finite R M) :
  N + (module.radical R M) = ⊤ → N = ⊤ := 
begin
  contrapose,
  intros hN hcont,
  obtain ⟨L, hLmax, hNL⟩ := exists_le_maximal h N hN,
  have : ⊤ ≤ L := hcont ▸ sup_le hNL (Inf_le hLmax),
  rw top_le_iff at this,
  exact hLmax.1 this,
end

-- Below: attempts for ideal version of Nakayama.
-- For now, there's no multiplication of (2-sided) ideal and (sub)modules, so we manually define it.
-- (Maybe there should be more useful definition.)

instance has_scalar'' : has_scalar (ideal R) (submodule R M) :=
{ smul := λ I N,
  span R { m | ∃ r ∈ I, ∃ n ∈ N, m = r • n }}

lemma ring_radical_smul_top_leq_module_radical (h : module.finite R M) :
  (ring.radical R) • (⊤ : submodule R M) ≤ module.radical R M :=
sorry

/--
Another Nakayama.
$N + (rad R) M = N$ implies $N = M$
-/
theorem eq_top_of_self_add_smul_radical_smul_top_eq_top
  (N : submodule R M) (h : module.finite R M) :
  N + (ring.radical R) • (⊤ : submodule R M) = ⊤ → N = ⊤ := 
begin
  sorry
end

end submodule