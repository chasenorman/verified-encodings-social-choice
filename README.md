# Verified Social Choice

This repository is in connection with the paper Impossibility Theorems Involving Weakenings of Expansion Consistency and Resoluteness in Voting by Wesley H. Holliday, Chase Norman, Eric Pacuit, Saam Zahedian. In particular, we generate a verifyably correct SAT encoding to prove Proposition B.3. A discussion of the formalism and encoding can be found in Appendix C. This verification is built on top of the [Verified Encodings](https://github.com/ccodel/verified-encodings) project by Cayden Codel. An alternate method to generate a CNF verifying Proposition B.3 can be found [here](https://github.com/szahedian/binary-gamma).

## Key Files

`src/demos/main.lean` contains the definition of the encoding, along with the proof `encodes_binary_gamma` proving that a tournament solution satisfying binary gamma implies the satisfyability of the CNF. This file also defines the types `graph` and `graph_embedding`.

`src/demos/graphs.lean` and `src/demos/embeddings.lean` contain the definitions of the graphs and embeddings used in the impossibily result. These definitions include proofs of key properties, such as the graphs being uniquely weighted.

Finally, `src/demos/generate_cnf.lean` creates the encoding using the graphs and embeddings and prints it as a CNF formula. The resulting formula is `generated.cnf`.

To demonstrate the unsatisfiability of `generated.cnf` we provide a Jupyter Notebook `VerifyUnsat.ipynb` containing code to evaluate the CNF formula on the 13 available SAT solvers in `pysat`.

## Installation

You can install Lean 3 following the instructions at [https://leanprover-community.github.io/get_started.html#regular-install](https://leanprover-community.github.io/get_started.html#regular-install).

Assuming you have Lean installed, you can fetch and build this repository as follows:

```bash
  leanproject get chasenorman/verified-encodings-social-choice
  cd verified-encodings-social-choice
  leanproject build
```
You can then open folder in VS Code and browse the files.