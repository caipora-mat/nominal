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

### Restante
1. **`Unification/Properties.lean`** (~36 erros): mecânicos (`subst_cons` →
   `subst_singleton`; `subst_append` → `subst_comp`, sed direto) + o cascade do
   σ-prefix:
   - `unifStep_σ_extends` / `unify_σ_prefix` afirmam `σ' = σ ++ ε` — falso em
     geral, verdadeiro sob a invariante (via `comp_singleton_eq_append`).
     Threadear `IsIdempotent`+`disjointPr` e reaplicar o bridge; ou restatar em
     nível de ação (`∀ t, t.subst σ' = (t.subst σ).subst ε`, vale por `subst_comp`).
   - `unifStep_next_idempotent_and_disjoint`: usar `comp_singleton`; provar
     `Subst.dom_comp : dom (σ.comp τ) = dom σ ∪ dom τ` (idêntico ao append).
   - `unifStep_next_sound`, `unify_sound` consomem `σ' = σ_next ++ extra`.
2. **`Completeness.lean`** (~4 mecânicos + `absorbedBy_append` → versão comp).
3. **`Mgu.lean`** (~6 mecânicos; caso instanciação passa a `σ.comp [binding]`).

## Estratégia recomendada

Chave: **`comp_singleton_eq_append`** sob a invariante. Onde as provas usavam
`σ ++ [binding]` / `subst_append`, reescrever comp → append (bridge) e reusar o
raciocínio de `applyOne` (occurs-check, estabilidade, disjunção). Provar
`Subst.dom_comp` cedo destrava todo o raciocínio de domínio.

## Nota

A branch `murillo/Syntax` permanece **zero-sorry** e é a versão a defender. Esta
refatoração é melhoria de fundação (semântica canônica), sem ganho de resultado
matemático — completude/principalidade valem igual nas duas.
