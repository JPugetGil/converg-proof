# ConVerG — Rocq formalization of condensed SPARQL evaluation

Formalization, in Rocq 9.0 (Rocq Platform 2025.08), of Chapters 5–6 of the
thesis *Querying of Multi-Version RDF Knowledge Graphs through Condensed
Representations*: the flat and condensed models, the flat and condensed
SPARQL algebras, the translation τ with representation promotion Υ, and the
evaluation equivalence theorem (Theorem 6.2) with its corollaries.

Every result is fully proved: there is no `Admitted`. The only assumptions
are the modeling parameters listed below.

## Build

```
rocq makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

## Files (in dependency order)

| File | Content | Thesis |
|------|---------|--------|
| `RDF.v` | terms, quads, variables | Ch. 3 |
| `ListUtil.v` | list lemmas (`filter_map`, `flat_map`, `Permutation`, `NoDup`) | — |
| `Versioning.v` | versions, versioned IRIs `VI(v, g)` (injective, `VI ⊂ I`), versioned quads, version sets | Def. 3.1, 5.1 |
| `Models.v` | flat model, condensed model, condensation `C`, flattening `F`, `C∘F = id`, `F∘C = id`, bag form of model correspondence | Def. 5.4–5.6, Thm 6.1 |
| `Representations.v` | dictionary encoding (bijection), representations `ψ ≤ ζ ≤ ι ≤ ν`, meet/join | Def. 5.3, 5.18 |
| `Environments.v` | environments `Γ`, raising | Def. 5.19 |
| `SolutionMappings.v` | bindings, flat/condensed mappings, expansion `Ξ`, cardinality, compatibility and merge in both algebras, Lemmas 6.3 (value preservation), 6.4 (compatibility preservation, both directions: `compat_flat_expand_cond`, `compat_cond_expand_flat`), 6.6 (join cardinality, as a `Permutation`: `expand_merge_perm`), 6.7 (multiplicative cardinality: `expand_length`) | Def. 5.7, 5.8, 5.20–5.26, 5.39 |
| `Expressions.v` | SPARQL expressions, evaluation over a partial lookup, conditions | §5.2 |
| `Promotion.v` | promotion `Υ` per binding / variable / mapping; Lemmas 6.1 and 6.2 (expansion preserved) | Def. 5.36 |
| `Difference.v` | product-set difference as disjoint slices (Lemma 5.1), residual over several blockers, condensed `DIFF` and its equivalence with the flat `DIFF` | Def. 5.29, 5.30 |
| `Typing.v` | environments as invariants (`env_ok`), pointwise meet, requirements `needs` | Def. 5.38, §5.5 |
| `FlatAlgebra.v`, `CondensedAlgebra.v` | syntax of both algebras (`TransformReprC` is `Υ`) | Def. 5.9–5.17, 5.27–5.37 |
| `FlatEvaluation.v`, `CondensedEvaluation.v` | evaluation `⟦e⟧_F(d_F)` and `⟦e⟧_C(d_C)` | §5.2, §5.3 |
| `Translation.v` | translation `τ` with result environment `R(e)` | Def. 5.40–5.41 |
| `TypeSystem.v` | typing judgement `typed E_C Γ` of condensed expressions, erasure of promotions, `translate_typed` (τ produces well-typed expressions) | Def. 5.38 |
| `Equivalence.v` | per-operator lemmas, `typed_correct` (type soundness + equivalence for every well-typed condensed expression), **`evaluation_equivalence`** (Thm 6.2 for τ), `count_preservation`, `multiplicity_preservation` | Thm 6.2 |

## Main statements

For every well-typed condensed expression `E_C` (judgement `typed E_C Γ`,
Definition 5.38), with `erase E_C` the flat expression obtained by forgetting
the promotions `Υ`:

```coq
Theorem typed_evaluation_equivalence : forall ec env dF dC,
  typed ec env -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat (erase ec) dF) (flat_map expand (eval_cond ec dC)).

Theorem type_soundness : forall ec env dC,
  typed ec env -> wf_condensed_model dC ->
  Forall (fun m => wf_cmap m /\ env_ok env m) (eval_cond ec dC).
```

For the translation `τ` (`translate_typed` shows that `τ(e)` is well-typed
and erases to `e`):

```coq
Theorem evaluation_equivalence : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat e dF)
              (flat_map expand (eval_cond (translate_expr e) dC)).
```

Bag semantics: solution sequences are lists and `≅` is `Permutation`.
`expand` is `Ξ`. `wf_flat_expr` is the thesis's unique-naming assumption
(no repeated variable in a quad pattern, fresh variable in `BIND`);
`wf_condensed_model` says that the condensed model is a function with
non-empty, duplicate-free version sets. The typing judgement carries the
same conditions (`TyQuadPattern`, `TyExtend`) and requires point-valued
variables (ι or ν) in the expressions of `FILTER`, `BIND`, `DIFF`,
`OPTIONAL` and for the variables dropped by `PROJECTION`.

Assumptions (checked with `Print Assumptions`): the abstract types
`IRI`, `Literal`, `Version` with decidable equality; `VI` injective;
the dictionary bijection `id_to_val`/`val_to_id`; the abstract semantics
of built-in functions and effective boolean values (`interp_func`, `ebv`,
`term_of_bool`), identical in both algebras.

## Corrections and choices with respect to the thesis

1. **Projection.** `Π_C` as stated is not equivalent to `Π_F` under bag
   semantics: projecting away a `ζ` variable bound to *n* versions turns
   *n* flat solutions into one condensed mapping of cardinality 1.
   The translation now promotes the projected-away variables to `ι`
   (`dropped_vars`) before `Π_C` (`projection_perm` has this hypothesis).
2. **Versioned IRIs are IRIs** (`vi : Version -> IRI -> IRI`), so that the
   graph variable of a flat mapping is bound to an RDF term; the inverse
   functions of Eq. (5.1) follow from injectivity.
3. **Merging of bindings** (`merge_binding`) is total and semantic:
   it represents `vals(b1) ∩ vals(b2)`. On two bindings of the same
   representation it coincides with Definitions 5.25–5.26; on mixed
   representations it keeps the point-valued binding.
4. **Environment of JOIN / UNION / OPTIONAL.** The result environment uses
   the pointwise *meet* on shared variables (`env_meet`), not the join:
   with the join, a variable that is `ι` on one side but may be unbound
   there (after `UNION` or `OPTIONAL`) and `ζ` on the other side would be
   declared point-valued while some results still carry a `ζ` binding.
   Environments are lower bounds on representations (`env_ok`); any extra
   promotion is harmless for correctness.
5. **Difference** needs non-empty version sets in the results (otherwise a
   condensed mapping with an empty `ζ` binding has no expansion but is
   still a mapping); this is the `wf_cmap` invariant, maintained by all
   operators and established by `wf_condensed_model`.
6. **Scope.** Grouping/aggregation (Def. 5.14–5.15) and the `ψ`
   representation (unbound graph variables) are not formalized; the graph
   position of a quad pattern is a variable.
