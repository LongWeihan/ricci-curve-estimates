# Mathematical blueprint data

`blueprint.json` contains 22 selected mathematical nodes mapping to 62 selected declarations. It is the data source for the offline review browser.

## Schema (version 1)

Top-level fields: `schema_version`, `title`, `language`, `scope`, `dependency_semantics`, `notation`, `references`, `nodes`.

Each node has:

- `id`: stable ASCII identifier; `title`: English heading; `kind`: `definition` or `theorem`.
- `math_statement`: English/LaTeX mathematical summary without outer display delimiters. A renderer may wrap it in display math. It is explanatory notation, not the exact Lean type; read the mapped declaration for every formal hypothesis.
- `explanation`: a short account of how the result is used.
- `lean`: entries with importable `module`, repository-relative `file`, and exact fully qualified `declarations`.
- `dependencies`: other node ids needed by the mathematical exposition. Edges are directed from a node to its prerequisites. These are curated narrative dependencies, neither complete import dependencies nor Lean constant-dependency claims.
- `source_references`: ids in top-level `references`.
- `contribution`: `category` (`reused`, `adapted`, or `new formalization`) and `detail`. This classifies formalization work, not mathematical novelty. A mixed node explains its reuse explicitly.
- `scope_caveats`: limitations and distinctions needed to read the statement accurately.

## Verification contract

For each `lean` entry, import `module` and check that every string in `declarations` names an existing Lean declaration. Do not infer theorems from comments or prove a weaker restatement just to validate the browser. The author checked all mappings against the current per-file compiled audit inventories when generating this data; CI should independently resolve them in the Lean environment. The main agent owns that checker and the rendered browser.

Also validate unique node ids, reference ids, existing dependency targets, and acyclicity. Source files are relative to the project root (the parent of this directory). Do not interpret narrative edges as proof-kernel dependency evidence; consult the actual declarations and `verification/` for that evidence.

## Scope

The chain starts with genuine Ricci flow and existing smooth immersed closed curve flows. It includes the corrected connection-variation terms, positive regularization, moving arclength integration, closed-endpoint comparison, compact ambient constants, real product geometry, and uniform estimates for arbitrary supplied static one-dimensional factor metrics. The positive-scale root selects constants before the entire metric and curve family.

The application node constructs the actual scaled metric from a supplied smooth one-dimensional metric. The project does not assert an unregularized total-curvature local-AC/a.e. theorem, construct AddCircle atlases, prove ramp/flow existence or continuation, or prove finite extinction or the Poincare conjecture itself. See `../docs/contribution-map.md` and the semantic-review documents for the precise adaptation boundaries.

## LaTeX escaping

Pass the parsed `math_statement` string directly to KaTeX/MathJax; do not unescape it again. JSON serialization escapes each literal backslash, but after JSON parsing commands contain exactly one U+005C character. The `flow_input` substring before `operatorname` has character codes `[45, 50, 92, 111, 112, 101]` (`-2`, one backslash, then `ope`).

The final node’s `cases` expression deliberately contains two backslashes for a row break immediately followed by the one-backslash `Theta` command. Those three consecutive U+005C characters are valid LaTeX and must be preserved; do not globally replace doubled backslashes in parsed strings.
