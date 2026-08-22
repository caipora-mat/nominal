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

1. **Def do algoritmo** (`Algorithm/Defs.lean:44,49,54`): trocar
   `σ ++ [binding]` por `Subst.comp σ [binding]` nos 3 casos de instanciação.
   A ação é idêntica (provado), então o unificador é o mesmo; o output passa a
   sair em forma resolvida.
2. **Terminação** (`Algorithm/Measure.lean`, `unifStep_next_decreasing`):
   revisar — a medida não depende de `σ`, então deve sobreviver quase intacta.
3. **Cascata de `σ ++ ε` → `comp`** (reformular enunciados/provas):
   - `unifStep_σ_extends` (σ_next = σ ++ ε; 16 casos)
   - `unifStep_next_idempotent_and_disjoint`, `instantiation_invariant`
   - `unify_le`, `absorbedBy_append`
   - `unifStep_next_binding_props` (Mgu)
4. **Mecânico `subst_cons`** (some sob simultânea; trocar por `subst_mvar_nil`/
   shape lemmas): Helpers ×5, Properties ×7, Completeness ×4, Mgu ×6.

## Estratégia recomendada

Usar o bridge: onde as provas antigas usavam `subst_append` para obter
`(t.subst σ).applyOne x u`, agora usar `subst_comp` + `subst_singleton`. Assim a
maior parte do raciocínio de `applyOne` (occurs-check, estabilidade, disjunção)
é reaproveitada sem reprovar do zero.

## Nota

A branch `murillo/Syntax` permanece **zero-sorry** e é a versão a defender. Esta
refatoração é melhoria de fundação (semântica canônica), sem ganho de resultado
matemático — completude/principalidade valem igual nas duas.
