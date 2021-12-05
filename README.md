# Generic Recursive Lens Combinators

This is the Agda implementation for _Generic Recursive Lens Combinators and Their Calculation Laws_. We use Agda 2.6.2 and `agda-stdlib` 1.7.

## Structure of This Repository

Main constructions:

- `Lens.agda`: Formalization of lenses (without contracts), provided for comparison
- `CLens.agda`: contract lenses without using containers<br>
  `Fixpoint.agda`: fixpoint "`μF = F μF`" and useful lemmas<br>
  **Note:** We had to turn off the positivity checker for the `μ` type, but it should be safe since all functors we passed to the `μ` type are indeed strictly positive (polynomial). In `CLens2`/`Fixpoint2`, we prove essentially the same results using container-based fixpoints, which completely solves the positivity problem. This version is still provided here because it is arguably easier to comprehend.
- `CLens2.agda`: contract lenses based on containers<br>
  `Fixpoint2.agda`: fixpoint and lemmas based on containers<br>
  As is said above, this version solves the positivity problem.
- `NContainer.agda`: formalization for N-ary containers<br>
  `NZip.agda`: `clift`, `fzip`, and related properties based on `NContainer`

Examples:
- `example/Tree.agda`: a binary tree. This example shows how accumulations should work on trees.
- `example/Tree2.agda`: a binary tree defined with containers:
  - We provided definitions of `clift` and `fzip`
  - We defined a bidirectional `F`-algebra `bmaxAlg`
  - We apply the `bFold` combinator with `bmaxAlg` to get `bmaximum`
  - We run the `bmaximum` and show the results

Supportive utilities:

- `Show.agda`: basic pretty-printing support
- `IntOmega.agda`: integer arithmetic extended to properly handle infinities
- `Utils.agda`: some common imports are gathered here<br>
  **Note:** we postulate functional extensionality here. This is the only axiom we assume, and this is safe because (according to PLFA):<br>
  > Postulating extensionality does not lead to difficulties, as it is known to be consistent with the theory that underlies Agda.

## Appendix: Outputs of the Two Examples

The output of the two examples is provided as follows for your convenience. One should be able to produce the exact same output.

### `example/Tree.agda`
- This is the original tree:
  ```
  +-3
  +-+-1
  | +-leaf
  | `-+-4
  |   +-leaf
  |   `-leaf
  `-leaf
  ```
- The result of `paths`:
  ```
  +-@tag: [(branch 3 _ _)]
  +-@val: 3
  +-+-@tag: [(branch 3 _ _),(branch 1 _ _)]
  | +-@val: 1
  | +-leaf: @tag: [(branch 3 _ _),(branch 1 _ _),leaf]
  | `-+-@tag: [(branch 3 _ _),(branch 1 _ _),(branch 4 _ _)]
  |   +-@val: 4
  |   +-leaf: @tag: [(branch 3 _ _),(branch 1 _ _),(branch 4 _ _),leaf]
  |   `-leaf: @tag: [(branch 3 _ _),(branch 1 _ _),(branch 4 _ _),leaf]
  `-leaf: @tag: [(branch 3 _ _),leaf]
  ```
- The result of `subtrees`:
  ```
  +-@tag: (branch 3 (branch 1 leaf (branch 4 leaf leaf)) leaf)
  +-@val: 3
  +-+-@tag: (branch 1 leaf (branch 4 leaf leaf))
  | +-@val: 1
  | +-leaf: @tag: leaf
  | `-+-@tag: (branch 4 leaf leaf)
  |   +-@val: 4
  |   +-leaf: @tag: leaf
  |   `-leaf: @tag: leaf
  `-leaf: @tag: leaf
  ```

### `example/Tree2.agda`

- First part of output is the same as `example/Tree.agda`.
- original tree:
  ```
  +-3
  +-+-1
  | +-leaf
  | `-+-4
  |   +-leaf
  |   `-leaf
  `-+-5
    +-+-13
    | +-+--2
    | | +-leaf
    | | `-leaf
    | `-leaf
    `-+-9
      +-leaf
      `-leaf
  ```
  Note the `+--2` should be interpreted as `+-(-2)` (the value at that node is `-2`).
- `get bmaximum`: 13
- `put bmaximum 2`:
  ```
  +-2
  +-+-1
  | +-leaf
  | `-+-2
  |   +-leaf
  |   `-leaf
  `-+-2
    +-+-2
    | +-+--2
    | | +-leaf
    | | `-leaf
    | `-leaf
    `-+-2
      +-leaf
      `-leaf
  ```
- `put bmaximum 7`:
  ```
  +-3
  +-+-1
  | +-leaf
  | `-+-4
  |   +-leaf
  |   `-leaf
  `-+-5
    +-+-7
    | +-+--2
    | | +-leaf
    | | `-leaf
    | `-leaf
    `-+-7
      +-leaf
      `-leaf
  ```