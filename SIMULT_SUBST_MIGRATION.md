# Migração para substituição simultânea — plano e estado

Branch `refactor/simult-subst`. Objetivo: trocar a substituição **sequencial**
(fold de `applyOne`) pela **simultânea** (uma passada, `lookup`), de modo que a
definição de substituição seja a padrão da literatura (Deivid) e o output do
algoritmo saia em forma resolvida (não triangular).

## Feito (verde, zero sorry)

- **`Substitution/Basic.lean`**
  - `Subst.lookup` + `ntm.subst` simultânea (uma passada).
  - Shape lemmas reprovados (`subst_atm/mvar/fapp/abs/permute/nil`).
  - `Subst.comp σ τ = σ.map(·.subst τ) ++ τ` (Martelli–Montanari) e a lei
    **`ntm.subst_comp : t.subst (σ.comp τ) = (t.subst σ).subst τ`** — o
    substituto correto de `subst_append` (que é FALSO sob simultânea).
- **`Substitution/Properties.lean`** — removido `subst_append` falso.
- **`Unification/Basic.lean`**
  - **Bridge `ntm.subst_singleton : t.subst [(x,u)] = t.applyOne x u`** — a peça
    que reaproveita toda a maquinaria de `applyOne` na semântica nova, e faz
    `σ.comp [(x,u)]` agir como o antigo `σ ++ [(x,u)]` (`t.subst(σ.comp[(x,u)])
    = (t.subst σ).applyOne x u`).
  - `subst_of_disjoint_dom` reprovado por indução no termo (via `lookup = none`).
  - `Subst.lookup_eq_none_iff_not_mem_dom`, `singleton_of_not_occursIn` adaptados.
  - **`append_singleton` → `comp_singleton`**: idempotência de `σ.comp [(x,u)]`.
  - Removido `applySubst_append` (falso, não usado).

## Falta

### Já feito nesta leva
- **Def do algoritmo** (`Algorithm/Defs.lean`): `σ ++ [binding]` → `σ.comp [binding]`
  nos 3 casos de instanciação. Verde; terminação intacta (medida independe de σ).
- **Bridge decisivo** (`Unification/Basic.lean`) **`Subst.comp_singleton_eq_append`**:
  se `x` não ocorre em nenhum valor de `σ`, `σ.comp [(x,u)] = σ ++ [(x,u)]`. Sob a
  invariante (binding fresco p/ o range de σ), comp colapsa em append — então o
  raciocínio baseado em `++` porta com `rw [← Subst.comp_singleton_eq_append hx]`.

### Feito — NÚCLEO COMPLETO (verde, zero sorry)
- **`Unification/Properties.lean`** (soundness): migrado. Chave foi o
  **restatement em nível de ação** do σ-prefix:
  `unifStep_σ_extends` / `unify_σ_prefix` viraram
  `∃ε ∀t, t.subst σ' = (t.subst σ).subst ε` (composição via `Subst.comp`, vale
  por `subst_comp`). `mvar_subst_eq_binding` / `unifStep_next_sound` tomam a
  hipótese de ação. `instantiation_invariant` usa `comp_singleton` + `dom_comp`.
- **`Unification/Completeness.lean`** (principalidade): migrado.
  `absorbedBy_append` → `absorbedBy_comp`; os 7 `heq` de instanciação passam a
  `σ.comp [binding]`. `solve_principal` compila, axiomas padrão.
- **`Subst.dom_comp`** (Basic): `dom (σ.comp τ) = dom σ ∪ dom τ`.

### Restante — só `Mgu.lean` (mediador explícito)
Precisa **rework conceitual**, não mecânico. `SimSubst.lean` foi criado para
DEFINIR a substituição simultânea quando `subst` era sequencial (`substSim`,
`normalize`, `reduce`, `subst_eq_substSim_normalize`). Agora `subst` JÁ é
simultânea, então:
- `substSim` e `subst` coincidem (provar `subst = substSim` diretamente, ou
  eliminar `substSim` e usar `subst`).
- `normalize`/`reduce` e a relação sequencial↔simultânea ficam redundantes ou
  se invertem — o mediador `solve_mediator_explicit` deve ser reescrito sobre a
  `subst` simultânea direta.
- Lemas de suporte já reprovados sob simultânea: `subst_avoids_dom_of_solved`,
  `subst_drop_dom` (agora por indução no termo, via `lookup`),
  `occursIn_subst_of_avoid`, `lookup_filter_not_mem_dom`, `lookup_mem`.
- Pendências pontuais: `subst_mvar_eq_lookupSim` (relacionar `lookup` e
  `lookupSim`), casos `MovesDom`/binding_props já em `comp`.

## Estratégia (para o restante do Mgu)

Como `subst` é simultânea, provavelmente **eliminar `SimSubst.lean`** e reescrever
o mediador diretamente: `solvedForm_mediator` + `solve_mediator_explicit` sobre
`subst`, usando `lookup`. Os lemas de forma resolvida (`SolvedForm`,
`subst_avoids_dom_of_solved`, `subst_drop_dom`) já estão prontos e são o núcleo
do mediador.

## Nota

A branch `murillo/Syntax` permanece **zero-sorry** e é a versão a defender. Esta
refatoração é melhoria de fundação (semântica canônica), sem ganho de resultado
matemático — completude/principalidade valem igual nas duas.

---

## ✅ CONCLUÍDA (todos os arquivos verdes, zero sorry)

Toda a árvore migrada para substituição simultânea:
- Substitution/Basic, Properties; Unification/Basic, Algorithm, Helpers,
  Properties (soundness), Completeness (principalidade), Mgu (mediador).
- `solve_principal`, `solve_mediator_explicit` e `solve_factors_comp` dependem
  apenas dos axiomas padrão (`propext`, `Classical.choice`, `Quot.sound`).

**Resultado novo, só possível com a simultânea:**
`UnifProblem.solve_factors_comp` — a fatoração EXATA que o Daniel pediu:
para o output σ do solve e qualquer solução θ, existe σ' (= θ∖dom σ) com
domínio disjunto de dom σ tal que `∀X, Δ ⊢ X(σ.comp σ') ≈α Xθ`, i.e.
`σ.comp σ' = θ` como ação. Com `comp` sendo composição genuína (subst_comp),
isto é o "σ ++ σ' = θ" correto — não mais coincidência da aplicação sequencial.

Validação empírica: os 4 exemplos da Fig.1 (Maribel) produzem output idêntico
nas duas semânticas (sequencial vs simultânea).
