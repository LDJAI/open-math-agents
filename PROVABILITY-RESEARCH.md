# A proposed answer to Henriques's question, with Collatz and P versus NP research notes

The four-page manuscript gives a proposed negative resolution of André Henriques's 2010 operator-algebra question. The proof constructs a conditional expectation that forces finite index. It then invokes the finite-index contradiction posted by Ulrich Pennig in 2011. The complete operator-algebra theorem awaits independent expert review and an end-to-end Lean proof. Priority for the finite-index reduction is provisional.

[Read the research note](three-open-problems.pdf) · [Henriques's question and public partial result](https://mathoverflow.net/questions/47071/endomorphism-of-type-iii-factor-can-it-satisfy-phi-circ-phi-phi-oplus-phi) · [Published index theorems](https://ems.press/content/serial-article-files/36793)

| Catalogue entry | What the quotation predicts | What was checked |
| :--- | :--- | :--- |
| [Henriques's endomorphism](https://lefttosolve.com/p/mo-47071) | Henriques suspected the proposed irreducible endomorphism itself was impossible. | The averaging map, its fixed points and the composite bound F(x) ≥ x/16, with an explicit preimage in the fixed-point algebra. The manuscript gives the remaining index and duality argument. |
| [Collatz](https://lefttosolve.com/p/CollatzConjecture.collatz_conjecture) | Conway thought the full conjecture very likely to be unsettleable. | Universal convergence is equivalent to eventual descent. A fixed step bound fails for every rank eventually nondecreasing within congruence classes of a fixed modulus. |
| [P versus NP](https://lefttosolve.com/p/ComplexityTheory.P_ne_NP) | Dória predicted independence from ZFC and a proof using an extra large-cardinal hypothesis. | A family of satisfiable formulas has exactly exponentially many residual functions after a variable cut. This refutes an inference from residual count alone to SAT decision time. |

The two predictions about provability and Henriques's prediction about existence answer different questions. No result here settles Collatz or P versus NP. No solution was submitted to Left To Solve.

## Checking the formal work

Use Lean 4.33.1 with the dependency environment from google-deepmind/formal-conjectures at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Its mathlib revision is 0df444a360eaa60ab8c11dca51a86af692955474. From a prepared checkout of that revision, run the following command with the path to the extracted files.

    lake env bash /absolute/path/to/verify-provability.sh

The script builds the local modules in dependency order and prints their axiom reports. The recorded run is in verification.txt. All reported dependencies are among propext, Classical.choice and Quot.sound. The files use explicit premises for objects and maps in the operator-algebra lemmas. No catalogue conjecture is imported as an axiom.
